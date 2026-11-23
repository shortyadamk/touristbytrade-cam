package com.monocam

import android.Manifest
import android.animation.Animator
import android.animation.AnimatorListenerAdapter
import android.animation.ValueAnimator
import android.app.AlertDialog
import android.content.ContentUris
import android.content.ContentValues
import android.content.Context
import android.content.Intent
import android.content.SharedPreferences
import android.content.pm.PackageManager
import android.content.res.ColorStateList
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.BitmapShader
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.ColorMatrix
import android.graphics.ColorMatrixColorFilter
import android.graphics.Matrix
import android.graphics.Paint
import android.graphics.Shader
import android.graphics.drawable.GradientDrawable
import android.hardware.camera2.CameraCharacteristics
import android.hardware.camera2.CameraManager
import android.media.ExifInterface
import android.os.Bundle
import android.os.Environment
import android.provider.MediaStore
import android.text.InputFilter
import android.util.Size
import android.view.Gravity
import android.view.HapticFeedbackConstants
import android.view.MotionEvent
import android.view.OrientationEventListener
import android.view.ScaleGestureDetector
import android.view.Surface
import android.view.TextureView
import android.view.View
import android.view.ViewGroup
import android.widget.Button
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.ImageView
import android.widget.LinearLayout
import android.widget.ProgressBar
import android.widget.ScrollView
import android.widget.SeekBar
import android.widget.TextView
import android.widget.Toast
import androidx.activity.ComponentActivity
import androidx.activity.result.contract.ActivityResultContracts
import androidx.camera.core.Camera
import androidx.camera.core.CameraSelector
import androidx.camera.core.FocusMeteringAction
import androidx.camera.core.ImageCapture
import androidx.camera.core.ImageCaptureException
import androidx.camera.core.ImageProxy
import androidx.camera.core.Preview
import androidx.camera.core.ZoomState
import androidx.camera.core.resolutionselector.AspectRatioStrategy
import androidx.camera.core.resolutionselector.ResolutionSelector
import androidx.camera.core.resolutionselector.ResolutionStrategy
import androidx.camera.extensions.ExtensionMode
import androidx.camera.extensions.ExtensionsManager
import androidx.camera.lifecycle.ProcessCameraProvider
import androidx.camera.view.PreviewView
import androidx.core.content.ContextCompat
import androidx.core.view.ViewCompat
import androidx.core.view.WindowCompat
import androidx.core.view.WindowInsetsCompat
import androidx.lifecycle.Observer
import java.io.ByteArrayInputStream
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.util.Random
import java.util.concurrent.Executors
import java.util.concurrent.Future
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicInteger
import kotlin.math.abs
import kotlin.math.ceil
import kotlin.math.hypot
import kotlin.math.max
import kotlin.math.min
import kotlin.math.roundToInt
import kotlin.math.sqrt

private const val MATCH = ViewGroup.LayoutParams.MATCH_PARENT
private const val WRAP = ViewGroup.LayoutParams.WRAP_CONTENT
private const val MAX_PENDING = 8

// true = best image quality (slightly slower capture), false = fastest capture
private const val CAPTURE_MAX_QUALITY = true

// height of the slide-out settings area (tabs 46dp + sliders 190dp)
private const val SETTINGS_DP = 236

private val TEAL = Color.parseColor("#3FA79D")
private val GRAY = Color.parseColor("#3A3A3A")

// one set of slider values: exposure, contrast, saturation, warmth, grain, grain size
private class St(
    var ev: Float, var ct: Float, var sat: Float,
    var warm: Float, var gr: Float, var gs: Float
) {
    fun set(a: FloatArray) {
        ev = a[0]; ct = a[1]; sat = a[2]; warm = a[3]; gr = a[4]; gs = a[5]
    }

    fun arr() = floatArrayOf(ev, ct, sat, warm, gr, gs)
}

// the look that was active at the moment the shutter was pressed
private class Look(
    val color: Boolean, val ct: Float, val sat: Float,
    val warm: Float, val grain: Float, val size: Float
)

private fun bw(ev: Float, ct: Float, gr: Float, gs: Float) = floatArrayOf(ev, ct, 0f, 0f, gr, gs)
private fun col(ev: Float, ct: Float, sat: Float, warm: Float, gr: Float) =
    floatArrayOf(ev, ct, sat, warm, gr, 1.5f)

// saturation, warmth and contrast in one color matrix (sat 0 = black and white)
private fun colorMatrix(ct: Float, sat: Float, warm: Float): ColorMatrix {
    val lr = 0.299f
    val lg = 0.587f
    val lb = 0.114f
    val rg = (1f + 0.25f * warm) * ct
    val gg = ct
    val bg = (1f - 0.25f * warm) * ct
    val t = 128f * (1f - ct)
    val ia = 1f - sat
    return ColorMatrix(
        floatArrayOf(
            (ia * lr + sat) * rg, ia * lg * rg, ia * lb * rg, 0f, t,
            ia * lr * gg, (ia * lg + sat) * gg, ia * lb * gg, 0f, t,
            ia * lr * bg, ia * lg * bg, (ia * lb + sat) * bg, 0f, t,
            0f, 0f, 0f, 1f, 0f
        )
    )
}

// how to turn the captured pixels upright: read the JPEG's rotation info, else use CameraX's value
private fun uprightMatrix(bytes: ByteArray, fallbackRot: Int): Matrix {
    val m = Matrix()
    var o = ExifInterface.ORIENTATION_UNDEFINED
    try {
        o = ExifInterface(ByteArrayInputStream(bytes))
            .getAttributeInt(ExifInterface.TAG_ORIENTATION, ExifInterface.ORIENTATION_UNDEFINED)
    } catch (e: Exception) {
    }
    when (o) {
        ExifInterface.ORIENTATION_NORMAL -> {}
        ExifInterface.ORIENTATION_ROTATE_90 -> m.postRotate(90f)
        ExifInterface.ORIENTATION_ROTATE_180 -> m.postRotate(180f)
        ExifInterface.ORIENTATION_ROTATE_270 -> m.postRotate(270f)
        ExifInterface.ORIENTATION_FLIP_HORIZONTAL -> m.postScale(-1f, 1f)
        ExifInterface.ORIENTATION_FLIP_VERTICAL -> m.postScale(1f, -1f)
        ExifInterface.ORIENTATION_TRANSPOSE -> { m.postRotate(90f); m.postScale(-1f, 1f) }
        ExifInterface.ORIENTATION_TRANSVERSE -> { m.postRotate(270f); m.postScale(-1f, 1f) }
        else -> if (fallbackRot != 0) m.postRotate(fallbackRot.toFloat())
    }
    return m
}

class MainActivity : ComponentActivity() {

    private lateinit var prefs: SharedPreferences
    private lateinit var previewView: PreviewView
    private lateinit var grainView: GrainView
    private lateinit var thumb: ImageView
    private lateinit var thumbDim: View
    private lateinit var thumbSpinner: ProgressBar
    private lateinit var thumbCount: TextView
    private lateinit var lensRow: LinearLayout
    private lateinit var zoomLabel: TextView
    private lateinit var ring: View
    private lateinit var flash: View
    private lateinit var shutterBtn: View
    private lateinit var saveBtn: Button
    private lateinit var adjustView: LinearLayout
    private lateinit var presetView: LinearLayout
    private lateinit var tabAdjust: Button
    private lateinit var tabPresets: Button
    private lateinit var modeBtn: Button
    private lateinit var extBtn: Button
    private lateinit var settings: LinearLayout
    private lateinit var handle: TextView
    private lateinit var orient: OrientationEventListener

    private var camera: Camera? = null
    private var imageCapture: ImageCapture? = null
    private var provider: ProcessCameraProvider? = null
    private var lens = CameraSelector.LENS_FACING_BACK
    private var sensorRot = Surface.ROTATION_0

    private var settingsOpen = false
    private var settingsAnim: ValueAnimator? = null

    // Google's HDR / Night processing (camera extensions): 0 = standard, 1 = HDR, 2 = Night
    private var extMgr: ExtensionsManager? = null
    private val extCodes = intArrayOf(ExtensionMode.NONE, ExtensionMode.HDR, ExtensionMode.NIGHT)
    private val extNames = arrayOf("Std", "HDR", "Night")
    private var extMode = 0
    private var extActive = 0
    private var extAvail: List<Int> = listOf(0)

    // zoom ratios of the phone's real back lenses (ultrawide / main / tele), found once
    private var opticalStops: List<Float>? = null

    // 0 = black and white, 1 = color
    private var mode = 0
    private val sts = arrayOf(
        St(0f, 1.2f, 0f, 0f, 0.35f, 1.6f),
        St(0f, 1.0f, 1.0f, 0f, 0f, 1.5f)
    )
    private fun cur() = sts[mode]

    // capture callbacks run on one thread, processing on another, pixel work on a pool
    private val worker = Executors.newSingleThreadExecutor()
    private val processor = Executors.newSingleThreadExecutor()
    private val pixelPool = Executors.newFixedThreadPool(
        Runtime.getRuntime().availableProcessors().coerceIn(2, 6)
    )
    private val pending = AtomicInteger(0)
    private val seqCounter = AtomicInteger(0)

    private val bars = HashMap<String, SeekBar>()
    private val rows = HashMap<String, View>()
    private val progFns = HashMap<String, (St) -> Int>()

    // presets: [mode][slot]
    private val names = arrayOf(
        arrayOf("Neutral", "Punchy", "Gritty", "Soft", "High key", "Low key", "Noir", "Fade", "Street", "Clean"),
        arrayOf("Natural", "Vivid", "Warm", "Cool", "Film", "Fade", "Vintage", "Moody", "Golden", "Chrome")
    )
    private val defs = arrayOf(
        arrayOf(
            bw(0f, 1.0f, 0f, 1.5f),
            bw(-0.3f, 1.7f, 0.25f, 1.5f),
            bw(0.2f, 2.0f, 0.75f, 2.4f),
            bw(0.3f, 0.85f, 0.2f, 1.4f),
            bw(0.8f, 1.1f, 0.15f, 1.3f),
            bw(-0.8f, 1.8f, 0.3f, 1.6f),
            bw(-0.4f, 2.3f, 0.5f, 2.0f),
            bw(0.4f, 0.7f, 0.3f, 1.8f),
            bw(0f, 1.5f, 0.55f, 2.0f),
            bw(0f, 1.3f, 0f, 1.5f)
        ),
        arrayOf(
            col(0f, 1.0f, 1.0f, 0f, 0f),
            col(0f, 1.2f, 1.5f, 0.1f, 0f),
            col(0.1f, 1.05f, 1.1f, 0.5f, 0f),
            col(0f, 1.05f, 1.0f, -0.5f, 0f),
            col(0.1f, 1.1f, 0.85f, 0.2f, 0.4f),
            col(0.3f, 0.8f, 0.7f, 0.1f, 0.15f),
            col(0.1f, 0.95f, 0.7f, 0.45f, 0.5f),
            col(-0.5f, 1.3f, 0.75f, -0.25f, 0.3f),
            col(0.2f, 1.1f, 1.2f, 0.7f, 0.1f),
            col(-0.1f, 1.4f, 0.9f, -0.1f, 0.2f)
        )
    )
    private val bwMap = intArrayOf(0, 1, 4, 5)
    private val pn = Array(2) { Array(10) { "" } }
    private val pv = Array(2) { Array(10) { FloatArray(6) } }
    private val selP = intArrayOf(0, 0)
    private val presetButtons = ArrayList<Button>()

    // lenses / zoom
    private val lensItems = ArrayList<Pair<Float, TextView>>()
    private var lensBuilt = false
    private val zoomObserver = Observer<ZoomState> { zs -> onZoomState(zs) }

    private val permissionLauncher =
        registerForActivityResult(ActivityResultContracts.RequestPermission()) { ok ->
            if (ok) startCamera() else toast("Camera permission is needed to take photos")
        }

    private fun dp(v: Int) = (v * resources.displayMetrics.density).toInt()
    private fun toast(t: String) = Toast.makeText(this, t, Toast.LENGTH_SHORT).show()

    private fun styleBtn(b: Button, on: Boolean) {
        b.background = GradientDrawable().apply {
            cornerRadius = dp(8).toFloat()
            setColor(if (on) TEAL else GRAY)
        }
        b.setTextColor(Color.WHITE)
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        WindowCompat.setDecorFitsSystemWindows(window, false)
        window.statusBarColor = Color.BLACK
        window.navigationBarColor = Color.BLACK

        prefs = getSharedPreferences("mono", Context.MODE_PRIVATE)
        for (i in 0 until 10) {
            pn[0][i] = prefs.getString("pn$i", names[0][i]) ?: names[0][i]
            pv[0][i] = defs[0][i].copyOf()
            for (k in 0 until 4) {
                pv[0][i][bwMap[k]] = prefs.getFloat("pv${i}_$k", defs[0][i][bwMap[k]])
            }
            pn[1][i] = prefs.getString("cn$i", names[1][i]) ?: names[1][i]
            for (k in 0 until 6) pv[1][i][k] = prefs.getFloat("cv${i}_$k", defs[1][i][k])
        }
        sts[0].ev = prefs.getFloat("ev", 0f)
        sts[0].ct = prefs.getFloat("ct", 1.2f)
        sts[0].gr = prefs.getFloat("gr", 0.35f)
        sts[0].gs = prefs.getFloat("gs", 1.6f)
        sts[1].ev = prefs.getFloat("cev", 0f)
        sts[1].ct = prefs.getFloat("cct", 1.0f)
        sts[1].sat = prefs.getFloat("csat", 1.0f)
        sts[1].warm = prefs.getFloat("cwarm", 0f)
        sts[1].gr = prefs.getFloat("cgr", 0f)
        selP[0] = prefs.getInt("sel", 0).coerceIn(0, 9)
        selP[1] = prefs.getInt("csel", 0).coerceIn(0, 9)
        mode = prefs.getInt("mode", 0).coerceIn(0, 1)
        lens = prefs.getInt("lens", CameraSelector.LENS_FACING_BACK)
        extMode = prefs.getInt("ext", 0).coerceIn(0, 2)
        settingsOpen = prefs.getBoolean("settingsOpen", false)

        // follow the phone's physical orientation so landscape shots are saved upright
        orient = object : OrientationEventListener(this) {
            override fun onOrientationChanged(o: Int) {
                if (o == ORIENTATION_UNKNOWN) return
                val r = when {
                    o >= 315 || o < 45 -> Surface.ROTATION_0
                    o < 135 -> Surface.ROTATION_270
                    o < 225 -> Surface.ROTATION_180
                    else -> Surface.ROTATION_90
                }
                if (r != sensorRot) {
                    sensorRot = r
                    imageCapture?.targetRotation = r
                }
            }
        }

        previewView = PreviewView(this).apply {
            implementationMode = PreviewView.ImplementationMode.COMPATIBLE
            scaleType = PreviewView.ScaleType.FILL_CENTER
        }
        grainView = GrainView(this)

        lensRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER
            minimumHeight = dp(54)
        }
        zoomLabel = TextView(this).apply {
            setTextColor(Color.WHITE)
            textSize = 14f
            visibility = View.GONE
        }
        ring = View(this).apply {
            background = GradientDrawable().apply {
                shape = GradientDrawable.OVAL
                setColor(Color.TRANSPARENT)
                setStroke(dp(2), Color.WHITE)
            }
            visibility = View.GONE
        }
        flash = View(this).apply {
            setBackgroundColor(Color.BLACK)
            alpha = 0f
        }

        // HDR / Night button (lives in the right-hand button column, not on the image)
        extBtn = Button(this).apply {
            isAllCaps = false
            textSize = 11f
            minWidth = 0
            minimumWidth = 0
            minHeight = 0
            minimumHeight = 0
            setPadding(0, 0, 0, 0)
            setOnClickListener { cycleExt() }
        }
        styleExt()

        val frame = FrameLayout(this).apply {
            setBackgroundColor(Color.BLACK)
            addView(previewView, MATCH, MATCH)
            addView(grainView, MATCH, MATCH)
            addView(flash, MATCH, MATCH)
            addView(ring, dp(64), dp(64))
            addView(zoomLabel, FrameLayout.LayoutParams(WRAP, WRAP).apply {
                gravity = Gravity.TOP or Gravity.CENTER_HORIZONTAL
                topMargin = dp(12)
            })
        }
        setupTouch(frame)

        // ----- adjust tab (all rows exist; some are hidden per mode) -----
        adjustView = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        addRow("ev", 40, { "Exposure %+.1f EV".format((it - 20) / 10f) },
            { ((it.ev * 10f).roundToInt() + 20).coerceIn(0, 40) }) { s, p -> s.ev = (p - 20) / 10f }
        addRow("ct", 100, { "Contrast %.2f".format(0.5f + it * 0.02f) },
            { ((it.ct - 0.5f) / 0.02f).roundToInt().coerceIn(0, 100) }) { s, p -> s.ct = 0.5f + p * 0.02f }
        addRow("sat", 100, { "Saturation %d%%".format(it * 2) },
            { (it.sat * 50f).roundToInt().coerceIn(0, 100) }) { s, p -> s.sat = p / 50f }
        addRow("warm", 200, { "Warmth %+d".format(it - 100) },
            { ((it.warm * 100f).roundToInt() + 100).coerceIn(0, 200) }) { s, p -> s.warm = (p - 100) / 100f }
        addRow("gr", 100, { "Grain %d%%".format(it) },
            { (it.gr * 100f).roundToInt().coerceIn(0, 100) }) { s, p -> s.gr = p / 100f }
        addRow("gs", 30, { "Grain size %.1f".format(1f + it / 10f) },
            { ((it.gs - 1f) * 10f).roundToInt().coerceIn(0, 30) }) { s, p -> s.gs = 1f + p / 10f }

        // ----- presets tab -----
        presetView = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            visibility = View.GONE
        }
        for (r in 0 until 2) {
            val row = LinearLayout(this).apply { orientation = LinearLayout.HORIZONTAL }
            for (c in 0 until 5) {
                val i = r * 5 + c
                val b = Button(this).apply {
                    textSize = 11f
                    isAllCaps = false
                    isSingleLine = true
                    minWidth = 0
                    minimumWidth = 0
                    setPadding(0, 0, 0, 0)
                    setOnClickListener { selectPreset(i) }
                    setOnLongClickListener { renamePreset(i); true }
                }
                presetButtons.add(b)
                val lp = LinearLayout.LayoutParams(0, dp(40), 1f)
                lp.setMargins(dp(2), dp(2), dp(2), dp(2))
                row.addView(b, lp)
            }
            presetView.addView(row, LinearLayout.LayoutParams(MATCH, WRAP))
        }
        saveBtn = Button(this).apply {
            isAllCaps = false
            setOnClickListener {
                val i = selP[mode]
                pv[mode][i] = cur().arr()
                savePreset(mode, i)
                toast("Saved to ${pn[mode][i]}")
            }
        }
        styleBtn(saveBtn, false)
        val slp = LinearLayout.LayoutParams(MATCH, dp(44))
        slp.setMargins(dp(2), dp(6), dp(2), dp(2))
        presetView.addView(saveBtn, slp)
        val hint = TextView(this).apply {
            text = "Tap to load. Long-press to rename."
            setTextColor(Color.parseColor("#888888"))
            textSize = 12f
            gravity = Gravity.CENTER
        }
        presetView.addView(hint, LinearLayout.LayoutParams(MATCH, WRAP))

        // ----- tabs -----
        tabAdjust = Button(this).apply {
            text = "Adjust"
            isAllCaps = false
            setOnClickListener { showTab(true) }
        }
        tabPresets = Button(this).apply {
            text = "Presets"
            isAllCaps = false
            setOnClickListener { showTab(false) }
        }
        val tabs = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            setPadding(dp(12), dp(4), dp(12), dp(2))
        }
        val t1 = LinearLayout.LayoutParams(0, dp(40), 1f)
        t1.setMargins(dp(2), 0, dp(2), 0)
        tabs.addView(tabAdjust, t1)
        val t2 = LinearLayout.LayoutParams(0, dp(40), 1f)
        t2.setMargins(dp(2), 0, dp(2), 0)
        tabs.addView(tabPresets, t2)
        showTab(true)

        val panel = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(dp(14), dp(2), dp(14), dp(6))
            addView(adjustView, MATCH, WRAP)
            addView(presetView, MATCH, WRAP)
        }
        val scroll = ScrollView(this).apply { addView(panel, MATCH, WRAP) }

        // ----- slide-out settings area (tabs + sliders / presets) -----
        settings = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            addView(tabs, LinearLayout.LayoutParams(MATCH, dp(46)))
            addView(scroll, LinearLayout.LayoutParams(MATCH, dp(190)))
        }

        // slim bar that opens and closes the settings area
        handle = TextView(this).apply {
            textSize = 12f
            gravity = Gravity.CENTER
            setTextColor(Color.parseColor("#BBBBBB"))
            setBackgroundColor(Color.parseColor("#161616"))
            setOnClickListener { setSettingsOpen(!settingsOpen, true) }
        }
        // (the panel is not on screen yet, so this only sets the bar's label)
        setSettingsOpen(settingsOpen, false)

        // ----- gallery thumbnail with a busy spinner on top -----
        thumb = ImageView(this).apply {
            scaleType = ImageView.ScaleType.CENTER_CROP
            setBackgroundColor(Color.parseColor("#222222"))
        }
        thumbDim = View(this).apply {
            setBackgroundColor(Color.parseColor("#88000000"))
            visibility = View.GONE
        }
        thumbSpinner = ProgressBar(this).apply {
            isIndeterminate = true
            indeterminateTintList = ColorStateList.valueOf(Color.WHITE)
            visibility = View.GONE
        }
        thumbCount = TextView(this).apply {
            setTextColor(Color.WHITE)
            textSize = 11f
            setBackgroundColor(Color.parseColor("#AA000000"))
            setPadding(dp(5), 0, dp(5), 0)
            visibility = View.GONE
        }
        val thumbBox = FrameLayout(this).apply {
            addView(thumb, MATCH, MATCH)
            addView(thumbDim, MATCH, MATCH)
            addView(thumbSpinner, FrameLayout.LayoutParams(dp(26), dp(26), Gravity.CENTER))
            addView(thumbCount, FrameLayout.LayoutParams(WRAP, WRAP, Gravity.BOTTOM or Gravity.END))
            setOnClickListener { openGallery() }
        }

        // ----- pinned lower section: lenses + shutter row -----
        shutterBtn = View(this).apply {
            background = GradientDrawable().apply {
                shape = GradientDrawable.OVAL
                setColor(Color.WHITE)
                setStroke(dp(6), Color.parseColor("#666666"))
            }
            setOnClickListener { shoot() }
        }

        // right-hand column, top to bottom: B&W/Color, Std/HDR/Night, Flip
        modeBtn = Button(this).apply {
            isAllCaps = false
            textSize = 11f
            minWidth = 0
            minimumWidth = 0
            minHeight = 0
            minimumHeight = 0
            setPadding(0, 0, 0, 0)
            setOnClickListener { setMode(1 - mode) }
        }
        val flip = Button(this).apply {
            text = "Flip"
            isAllCaps = false
            textSize = 11f
            minWidth = 0
            minimumWidth = 0
            minHeight = 0
            minimumHeight = 0
            setPadding(0, 0, 0, 0)
            setOnClickListener {
                lens = if (lens == CameraSelector.LENS_FACING_BACK)
                    CameraSelector.LENS_FACING_FRONT else CameraSelector.LENS_FACING_BACK
                bindCamera()
            }
        }
        styleBtn(flip, false)

        val side = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            gravity = Gravity.CENTER_HORIZONTAL
        }
        val mlp = LinearLayout.LayoutParams(dp(60), dp(30))
        mlp.bottomMargin = dp(4)
        side.addView(modeBtn, mlp)
        val elp = LinearLayout.LayoutParams(dp(60), dp(30))
        elp.bottomMargin = dp(4)
        side.addView(extBtn, elp)
        side.addView(flip, LinearLayout.LayoutParams(dp(60), dp(30)))

        val bottom = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            setPadding(dp(14), dp(4), dp(14), dp(8))
        }
        bottom.addView(thumbBox, LinearLayout.LayoutParams(dp(52), dp(52)))
        bottom.addView(View(this), LinearLayout.LayoutParams(0, 1, 1f))
        bottom.addView(shutterBtn, LinearLayout.LayoutParams(dp(88), dp(88)))
        bottom.addView(View(this), LinearLayout.LayoutParams(0, 1, 1f))
        bottom.addView(side, LinearLayout.LayoutParams(dp(60), WRAP))

        val lower = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setBackgroundColor(Color.BLACK)
            addView(lensRow, MATCH, WRAP)
            addView(bottom, MATCH, WRAP)
        }

        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setBackgroundColor(Color.BLACK)
            addView(frame, LinearLayout.LayoutParams(MATCH, 0, 1f))
            addView(handle, LinearLayout.LayoutParams(MATCH, dp(34)))
            addView(settings, LinearLayout.LayoutParams(MATCH, if (settingsOpen) dp(SETTINGS_DP) else 0))
            addView(lower, LinearLayout.LayoutParams(MATCH, WRAP))
        }
        if (!settingsOpen) settings.visibility = View.GONE
        ViewCompat.setOnApplyWindowInsetsListener(root) { v, insets ->
            val b = insets.getInsets(WindowInsetsCompat.Type.systemBars())
            v.setPadding(b.left, b.top, b.right, b.bottom)
            insets
        }
        setContentView(root)

        setMode(mode)

        if (ContextCompat.checkSelfPermission(this, Manifest.permission.CAMERA)
            == PackageManager.PERMISSION_GRANTED
        ) startCamera() else permissionLauncher.launch(Manifest.permission.CAMERA)
    }

    override fun onResume() {
        super.onResume()
        if (orient.canDetectOrientation()) orient.enable()
        refreshThumb()
    }

    override fun onPause() {
        super.onPause()
        orient.disable()
        prefs.edit()
            .putFloat("ev", sts[0].ev).putFloat("ct", sts[0].ct)
            .putFloat("gr", sts[0].gr).putFloat("gs", sts[0].gs)
            .putFloat("cev", sts[1].ev).putFloat("cct", sts[1].ct)
            .putFloat("csat", sts[1].sat).putFloat("cwarm", sts[1].warm)
            .putFloat("cgr", sts[1].gr)
            .putInt("sel", selP[0]).putInt("csel", selP[1])
            .putInt("mode", mode).putInt("lens", lens)
            .putInt("ext", extMode)
            .putBoolean("settingsOpen", settingsOpen)
            .apply()
    }

    // ---------- slide-out settings ----------

    private fun setSettingsOpen(open: Boolean, animate: Boolean) {
        settingsOpen = open
        handle.text = if (open) "▼  Close" else "▲  Adjust & presets"
        // before the panel is on screen it has no layout info yet; its starting height is set when built
        val lp = settings.layoutParams ?: return
        val target = if (open) dp(SETTINGS_DP) else 0
        settingsAnim?.cancel()
        if (open) settings.visibility = View.VISIBLE
        if (!animate) {
            lp.height = target
            settings.layoutParams = lp
            if (!open) settings.visibility = View.GONE
            return
        }
        val a = ValueAnimator.ofInt(lp.height, target)
        a.duration = 220
        a.addUpdateListener {
            lp.height = it.animatedValue as Int
            settings.layoutParams = lp
        }
        a.addListener(object : AnimatorListenerAdapter() {
            private var cancelled = false
            override fun onAnimationCancel(animation: Animator) {
                cancelled = true
            }

            override fun onAnimationEnd(animation: Animator) {
                if (!cancelled && !open) settings.visibility = View.GONE
            }
        })
        settingsAnim = a
        a.start()
    }

    // ---------- HDR / Night (camera extensions) ----------

    private fun styleExt() {
        val avail = extAvail.size > 1
        extBtn.text = extNames[extActive]
        extBtn.alpha = if (avail) 1f else 0.55f
        extBtn.background = GradientDrawable().apply {
            cornerRadius = dp(8).toFloat()
            setColor(if (extActive != 0) TEAL else GRAY)
        }
        extBtn.setTextColor(Color.WHITE)
    }

    private fun cycleExt() {
        if (extAvail.size <= 1) {
            toast("This phone doesn't offer HDR or Night to other apps")
            return
        }
        val i = extAvail.indexOf(extActive)
        extMode = extAvail[(i + 1) % extAvail.size]
        if (extMode == 2) toast("Night: hold still, shots take a few seconds")
        bindCamera()
    }

    // which of HDR / Night the phone offers for this camera
    private fun availableExt(base: CameraSelector): List<Int> {
        val m = extMgr ?: return listOf(0)
        val l = arrayListOf(0)
        for (i in 1..2) {
            val ok = try {
                m.isExtensionAvailable(base, extCodes[i])
            } catch (e: Exception) {
                false
            }
            if (ok) l.add(i)
        }
        return l
    }

    // ---------- gallery ----------

    // always open the phone's main gallery app
    private fun openGallery() {
        try {
            val i = Intent.makeMainSelectorActivity(Intent.ACTION_MAIN, Intent.CATEGORY_APP_GALLERY)
            i.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            startActivity(i)
            return
        } catch (e: Exception) {
        }
        try {
            val i = Intent(Intent.ACTION_VIEW, MediaStore.Images.Media.EXTERNAL_CONTENT_URI)
            i.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            startActivity(i)
            return
        } catch (e: Exception) {
        }
        toast("No gallery app found")
    }

    // show the newest photo from Pictures/MonoCam on the thumbnail (blank if there are none)
    private fun refreshThumb() {
        if (pending.get() > 0) return
        processor.execute {
            var bmp: Bitmap? = null
            try {
                contentResolver.query(
                    MediaStore.Images.Media.EXTERNAL_CONTENT_URI,
                    arrayOf(MediaStore.Images.Media._ID),
                    MediaStore.Images.Media.RELATIVE_PATH + " LIKE ?",
                    arrayOf("Pictures/MonoCam%"),
                    MediaStore.Images.Media.DATE_ADDED + " DESC"
                )?.use { c ->
                    if (c.moveToFirst()) {
                        val uri = ContentUris.withAppendedId(
                            MediaStore.Images.Media.EXTERNAL_CONTENT_URI, c.getLong(0)
                        )
                        bmp = contentResolver.loadThumbnail(uri, Size(240, 240), null)
                    }
                }
            } catch (e: Exception) {
            }
            val b = bmp
            runOnUiThread { if (pending.get() == 0) thumb.setImageBitmap(b) }
        }
    }

    // ---------- mode ----------

    private fun setMode(m: Int) {
        mode = m
        val color = m == 1
        modeBtn.text = if (color) "Color" else "B&W"
        styleBtn(modeBtn, color)
        rows["sat"]?.visibility = if (color) View.VISIBLE else View.GONE
        rows["warm"]?.visibility = if (color) View.VISIBLE else View.GONE
        rows["gs"]?.visibility = if (color) View.GONE else View.VISIBLE
        syncBars()
        updatePresetUi()
        refreshLook()
    }

    private fun syncBars() {
        for ((k, bar) in bars) bar.progress = progFns[k]!!(cur())
    }

    // push the current look to the viewfinder
    private fun refreshLook() {
        val s = cur()
        grainView.amount = s.gr
        grainView.grainSize = s.gs
        grainView.invalidate()
        applyExposure()
        applyFilter()
    }

    // ---------- UI helpers ----------

    private fun showTab(adjust: Boolean) {
        adjustView.visibility = if (adjust) View.VISIBLE else View.GONE
        presetView.visibility = if (adjust) View.GONE else View.VISIBLE
        styleBtn(tabAdjust, adjust)
        styleBtn(tabPresets, !adjust)
    }

    private fun addRow(
        key: String, top: Int, text: (Int) -> String,
        toProg: (St) -> Int, setter: (St, Int) -> Unit
    ) {
        val label = TextView(this).apply { setTextColor(Color.WHITE); textSize = 13f }
        val init = toProg(cur())
        val bar = SeekBar(this).apply { this.max = top; progress = init }
        label.text = text(init)
        bar.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(s: SeekBar?, p: Int, fromUser: Boolean) {
                label.text = text(p)
                setter(cur(), p)
                refreshLook()
            }
            override fun onStartTrackingTouch(s: SeekBar?) {}
            override fun onStopTrackingTouch(s: SeekBar?) {}
        })
        bars[key] = bar
        progFns[key] = toProg
        val row = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
        }
        row.addView(label, LinearLayout.LayoutParams(dp(135), WRAP))
        row.addView(bar, LinearLayout.LayoutParams(0, dp(36), 1f))
        rows[key] = row
        adjustView.addView(row, LinearLayout.LayoutParams(MATCH, WRAP))
    }

    // spinner over the thumbnail while photos are still being processed
    private fun updateBusyUi() {
        runOnUiThread {
            val n = pending.get()
            val on = n > 0
            thumbDim.visibility = if (on) View.VISIBLE else View.GONE
            thumbSpinner.visibility = if (on) View.VISIBLE else View.GONE
            thumbCount.visibility = if (n > 1) View.VISIBLE else View.GONE
            thumbCount.text = n.toString()
        }
    }

    // ---------- presets ----------

    private fun selectPreset(i: Int) {
        selP[mode] = i
        cur().set(pv[mode][i])
        syncBars()
        updatePresetUi()
        refreshLook()
    }

    private fun updatePresetUi() {
        for (i in 0 until 10) {
            presetButtons[i].text = pn[mode][i]
            styleBtn(presetButtons[i], i == selP[mode])
        }
        saveBtn.text = "Save current look to ${pn[mode][selP[mode]]}"
    }

    private fun savePreset(m: Int, i: Int) {
        val e = prefs.edit()
        if (m == 0) {
            e.putString("pn$i", pn[0][i])
            for (k in 0 until 4) e.putFloat("pv${i}_$k", pv[0][i][bwMap[k]])
        } else {
            e.putString("cn$i", pn[1][i])
            for (k in 0 until 6) e.putFloat("cv${i}_$k", pv[1][i][k])
        }
        e.apply()
    }

    private fun renamePreset(i: Int) {
        val m = mode
        val et = EditText(this).apply {
            setText(pn[m][i])
            setSelection(text.length)
            filters = arrayOf(InputFilter.LengthFilter(10))
            isSingleLine = true
        }
        AlertDialog.Builder(this)
            .setTitle("Rename preset")
            .setView(et)
            .setPositiveButton("OK") { _, _ ->
                val t = et.text.toString().trim()
                if (t.isNotEmpty()) {
                    pn[m][i] = t
                    savePreset(m, i)
                    if (m == mode) updatePresetUi()
                }
            }
            .setNegativeButton("Cancel", null)
            .show()
    }

    // ---------- touch: tap to focus, pinch to zoom ----------

    private fun setupTouch(frame: View) {
        val scale = ScaleGestureDetector(this, object : ScaleGestureDetector.SimpleOnScaleGestureListener() {
            override fun onScale(d: ScaleGestureDetector): Boolean {
                val cam = camera ?: return true
                val zs = cam.cameraInfo.zoomState.value ?: return true
                val r = (zs.zoomRatio * d.scaleFactor).coerceIn(zs.minZoomRatio, zs.maxZoomRatio)
                cam.cameraControl.setZoomRatio(r)
                flashZoomLabel()
                return true
            }
        })
        var downX = 0f
        var downY = 0f
        var downT = 0L
        var multi = false
        frame.setOnTouchListener { _, e ->
            scale.onTouchEvent(e)
            when (e.actionMasked) {
                MotionEvent.ACTION_DOWN -> { downX = e.x; downY = e.y; downT = e.eventTime; multi = false }
                MotionEvent.ACTION_POINTER_DOWN -> multi = true
                MotionEvent.ACTION_UP -> {
                    if (!multi && !scale.isInProgress && e.eventTime - downT < 350 &&
                        hypot(e.x - downX, e.y - downY) < dp(16)
                    ) focusAt(e.x, e.y)
                }
            }
            true
        }
    }

    private fun focusAt(x: Float, y: Float) {
        val cam = camera ?: return
        val p = previewView.meteringPointFactory.createPoint(x, y)
        val action = FocusMeteringAction.Builder(
            p, FocusMeteringAction.FLAG_AF or FocusMeteringAction.FLAG_AE
        ).setAutoCancelDuration(5, TimeUnit.SECONDS).build()
        try {
            cam.cameraControl.startFocusAndMetering(action)
        } catch (e: Exception) {
        }
        ring.animate().cancel()
        ring.x = x - dp(32)
        ring.y = y - dp(32)
        ring.alpha = 1f
        ring.scaleX = 1.4f
        ring.scaleY = 1.4f
        ring.visibility = View.VISIBLE
        ring.animate().scaleX(1f).scaleY(1f).setDuration(200).withEndAction {
            ring.animate().alpha(0f).setStartDelay(900).setDuration(300)
                .withEndAction { ring.visibility = View.GONE }.start()
        }.start()
    }

    private fun flashZoomLabel() {
        zoomLabel.visibility = View.VISIBLE
        zoomLabel.removeCallbacks(hideZoom)
        zoomLabel.postDelayed(hideZoom, 900)
    }

    private val hideZoom = Runnable { zoomLabel.visibility = View.GONE }

    // ---------- lenses ----------

    private fun fmt(r: Float): String =
        if (abs(r - r.roundToInt()) < 0.01f) "${r.roundToInt()}x" else "%.1fx".format(r)

    // button label: snap to a whole number when it is very close (4.97x shows as 5x)
    private fun fmtLabel(r: Float): String =
        if (abs(r - r.roundToInt()) < 0.15f && r >= 1f) "${r.roundToInt()}x" else "%.1fx".format(r)

    // equivalent focal length (relative to sensor size) of one camera, 0 if unknown
    private fun eqFocal(c: CameraCharacteristics): Float {
        val f = c.get(CameraCharacteristics.LENS_INFO_AVAILABLE_FOCAL_LENGTHS)?.firstOrNull() ?: return 0f
        val s = c.get(CameraCharacteristics.SENSOR_INFO_PHYSICAL_SIZE) ?: return 0f
        val diag = sqrt(s.width * s.width + s.height * s.height)
        return if (diag > 0f) f / diag else 0f
    }

    // zoom ratios (relative to the main lens) of the phone's real back lenses
    private fun findOpticalStops(): List<Float> {
        try {
            val mgr = getSystemService(Context.CAMERA_SERVICE) as CameraManager
            var phys: Set<String> = emptySet()
            var logicalEq = 0f
            for (id in mgr.cameraIdList) {
                val c = mgr.getCameraCharacteristics(id)
                if (c.get(CameraCharacteristics.LENS_FACING) != CameraCharacteristics.LENS_FACING_BACK) continue
                val p = c.physicalCameraIds
                if (p.size > phys.size) {
                    phys = p
                    logicalEq = eqFocal(c)
                }
            }
            val eqs = ArrayList<Float>()
            for (id in phys) {
                val e = eqFocal(mgr.getCameraCharacteristics(id))
                if (e > 0f) eqs.add(e)
            }
            if (eqs.isEmpty()) return emptyList()
            eqs.sort()
            val mainEq = if (logicalEq > 0f) {
                eqs.minByOrNull { abs(it - logicalEq) } ?: eqs[0]
            } else {
                if (eqs.size >= 2) eqs[1] else eqs[0]
            }
            val ratios = ArrayList<Float>()
            for (e in eqs) {
                val r = e / mainEq
                if (ratios.none { abs(it - r) < 0.05f }) ratios.add(r)
            }
            return ratios
        } catch (e: Exception) {
            return emptyList()
        }
    }

    // only the real lenses get a button: ultrawide, main, telephoto (no digital 2x / 10x)
    private fun buildLens(min: Float, max: Float) {
        lensRow.removeAllViews()
        lensItems.clear()
        if (lens == CameraSelector.LENS_FACING_FRONT) return
        val stops = opticalStops ?: findOpticalStops().also { opticalStops = it }
        val targets = ArrayList<Float>()
        targets.add(1f)
        if (stops.isEmpty()) {
            if (min < 0.95f) targets.add(min)
        } else {
            for (r in stops) {
                if (r < 0.95f) targets.add(min)
                else if (r > 1.05f) targets.add(ceil(r * 10f) / 10f)
            }
        }
        val list = targets.filter { it >= min - 0.001f && it <= max + 0.001f }
            .distinctBy { (it * 10f).roundToInt() }
            .sorted()
        for (r in list) {
            val tv = TextView(this).apply {
                text = fmtLabel(r)
                textSize = 13f
                gravity = Gravity.CENTER
                setOnClickListener {
                    camera?.cameraControl?.setZoomRatio(r.coerceIn(min, max))
                }
            }
            val lp = LinearLayout.LayoutParams(dp(46), dp(46))
            lp.setMargins(dp(5), dp(4), dp(5), dp(4))
            lensRow.addView(tv, lp)
            lensItems.add(Pair(r, tv))
        }
    }

    private fun onZoomState(zs: ZoomState) {
        if (!lensBuilt) {
            buildLens(zs.minZoomRatio, zs.maxZoomRatio)
            lensBuilt = true
        }
        val z = zs.zoomRatio
        // between or beyond the real lenses the picture is a digital crop
        val isOptical = if (lensItems.isEmpty()) z < 1.03f
        else lensItems.any { abs(z - it.first) / it.first < 0.03f }
        zoomLabel.text = if (isOptical) fmt(z) else fmt(z) + " digital"
        for ((r, tv) in lensItems) {
            val on = abs(z - r) / r < 0.08f
            tv.background = GradientDrawable().apply {
                shape = GradientDrawable.OVAL
                setColor(if (on) Color.WHITE else GRAY)
            }
            tv.setTextColor(if (on) Color.BLACK else Color.WHITE)
        }
    }

    // ---------- camera ----------

    private fun startCamera() {
        val f = ProcessCameraProvider.getInstance(this)
        f.addListener({
            val prov = f.get()
            provider = prov
            try {
                val ef = ExtensionsManager.getInstanceAsync(this, prov)
                ef.addListener({
                    extMgr = try {
                        ef.get()
                    } catch (e: Exception) {
                        null
                    }
                    bindCamera()
                }, ContextCompat.getMainExecutor(this))
            } catch (e: Exception) {
                extMgr = null
                bindCamera()
            }
        }, ContextCompat.getMainExecutor(this))
    }

    private fun bindCamera() {
        val p = provider ?: return
        camera?.cameraInfo?.zoomState?.removeObserver(zoomObserver)
        lensBuilt = false
        lensRow.removeAllViews()
        lensItems.clear()

        val base = CameraSelector.Builder().requireLensFacing(lens).build()
        extAvail = availableExt(base)
        extActive = if (extMode in extAvail) extMode else 0
        styleExt()
        val activeName = extNames[extActive]

        val preview = Preview.Builder().build().also { it.setSurfaceProvider(previewView.surfaceProvider) }

        val ic: ImageCapture
        val selector: CameraSelector
        if (extActive != 0) {
            // HDR / Night: let Google's processing decide resolution and quality
            ic = ImageCapture.Builder().setTargetRotation(sensorRot).build()
            selector = extMgr?.getExtensionEnabledCameraSelector(base, extCodes[extActive]) ?: base
        } else {
            // highest resolution 4:3 photo the camera offers
            val resolution = ResolutionSelector.Builder()
                .setAspectRatioStrategy(AspectRatioStrategy.RATIO_4_3_FALLBACK_AUTO_STRATEGY)
                .setResolutionStrategy(ResolutionStrategy.HIGHEST_AVAILABLE_STRATEGY)
                .build()
            ic = ImageCapture.Builder()
                .setCaptureMode(
                    if (CAPTURE_MAX_QUALITY) ImageCapture.CAPTURE_MODE_MAXIMIZE_QUALITY
                    else ImageCapture.CAPTURE_MODE_MINIMIZE_LATENCY
                )
                .setResolutionSelector(resolution)
                .setJpegQuality(100)
                .setTargetRotation(sensorRot)
                .build()
            selector = base
        }
        imageCapture = ic

        try {
            p.unbindAll()
            val cam = p.bindToLifecycle(this, selector, preview, ic)
            camera = cam
            cam.cameraInfo.zoomState.observe(this, zoomObserver)
            applyExposure()
            applyFilter()
            previewView.postDelayed({ applyFilter() }, 500)
            previewView.postDelayed({ applyFilter() }, 1500)
        } catch (e: Exception) {
            if (extActive != 0) {
                extMode = 0
                toast("Couldn't start $activeName mode, using standard")
                bindCamera()
            } else {
                toast("Camera error: ${e.message}")
            }
        }
    }

    private fun applyExposure() {
        val cam = camera ?: return
        val st = cam.cameraInfo.exposureState
        if (!st.isExposureCompensationSupported) return
        val step = st.exposureCompensationStep.toFloat()
        if (step <= 0f) return
        val idx = (cur().ev / step).roundToInt()
            .coerceIn(st.exposureCompensationRange.lower, st.exposureCompensationRange.upper)
        cam.cameraControl.setExposureCompensationIndex(idx)
    }

    private fun lookPaint(ct: Float, sat: Float, warm: Float): Paint =
        Paint().apply { colorFilter = ColorMatrixColorFilter(colorMatrix(ct, sat, warm)) }

    // color or black and white look for the live preview.
    // The filter lives on the PreviewView only; any paint left on the inner TextureView is cleared,
    // so an old black and white filter can never override the color one.
    private fun applyFilter() {
        val s = cur()
        val paint = if (mode == 1) lookPaint(s.ct, s.sat, s.warm) else lookPaint(s.ct, 0f, 0f)
        findTexture(previewView)?.setLayerType(View.LAYER_TYPE_HARDWARE, null)
        previewView.setLayerType(View.LAYER_TYPE_HARDWARE, paint)
    }

    private fun findTexture(v: View): TextureView? {
        if (v is TextureView) return v
        if (v is ViewGroup) {
            for (i in 0 until v.childCount) findTexture(v.getChildAt(i))?.let { return it }
        }
        return null
    }

    // ---------- capture ----------

    private fun shoot() {
        val ic = imageCapture ?: return
        if (pending.get() >= MAX_PENDING) {
            toast("Catching up, one moment")
            return
        }
        pending.incrementAndGet()
        updateBusyUi()
        val seq = seqCounter.incrementAndGet()
        val s = cur()
        val isColor = mode == 1
        val look = Look(
            isColor, s.ct,
            if (isColor) s.sat else 0f,
            if (isColor) s.warm else 0f,
            s.gr, s.gs
        )

        // instant feedback: vibration, shutter blink, button squish
        shutterBtn.performHapticFeedback(HapticFeedbackConstants.VIRTUAL_KEY)
        flash.animate().cancel()
        flash.alpha = 0.9f
        flash.animate().alpha(0f).setDuration(200).start()
        shutterBtn.animate().cancel()
        shutterBtn.animate().scaleX(0.9f).scaleY(0.9f).setDuration(60).withEndAction {
            shutterBtn.animate().scaleX(1f).scaleY(1f).setDuration(120).start()
        }.start()

        ic.takePicture(worker, object : ImageCapture.OnImageCapturedCallback() {
            override fun onCaptureSuccess(image: ImageProxy) {
                var raw: ByteArray? = null
                var rot = 0
                try {
                    rot = image.imageInfo.rotationDegrees
                    val buf = image.planes[0].buffer
                    buf.rewind()
                    val arr = ByteArray(buf.remaining())
                    buf.get(arr)
                    raw = arr
                } catch (t: Throwable) {
                    raw = null
                } finally {
                    // release the camera buffer right away so the next shot can start
                    image.close()
                }
                val data: ByteArray = raw ?: run {
                    pending.decrementAndGet()
                    updateBusyUi()
                    return
                }
                val mx = uprightMatrix(data, rot)
                try {
                    quickThumb(data, Matrix(mx), look)
                } catch (t: Throwable) {
                }
                processor.execute { process(data, mx, look, seq) }
            }

            override fun onError(exception: ImageCaptureException) {
                pending.decrementAndGet()
                updateBusyUi()
                runOnUiThread { toast("Capture failed: ${exception.message}") }
            }
        })
    }

    // fast, small preview of the shot, shown as soon as it is captured
    private fun quickThumb(bytes: ByteArray, mx: Matrix, look: Look) {
        val o = BitmapFactory.Options().apply { inSampleSize = 16 }
        val s = BitmapFactory.decodeByteArray(bytes, 0, bytes.size, o) ?: return
        val r = Bitmap.createBitmap(s, 0, 0, s.width, s.height, mx, true)
        val out = Bitmap.createBitmap(r.width, r.height, Bitmap.Config.ARGB_8888)
        Canvas(out).drawBitmap(r, 0f, 0f, lookPaint(look.ct, look.sat, look.warm))
        runOnUiThread { thumb.setImageBitmap(out) }
    }

    // full-resolution processing and saving, one photo at a time in the background
    private fun process(bytes: ByteArray, mx: Matrix, look: Look, seq: Int) {
        try {
            var bmp = BitmapFactory.decodeByteArray(bytes, 0, bytes.size)
                ?: throw IllegalStateException("could not decode photo")
            if (!mx.isIdentity) {
                val r = Bitmap.createBitmap(bmp, 0, 0, bmp.width, bmp.height, mx, true)
                bmp.recycle()
                bmp = r
            }
            val out = develop(bmp, look)
            bmp.recycle()
            save(out, seq, look.color)
            out.recycle()
        } catch (t: Throwable) {
            runOnUiThread { toast("Could not save photo: ${t.message}") }
        } finally {
            pending.decrementAndGet()
            updateBusyUi()
        }
    }

    // full-resolution look (black and white or color), contrast and grain, on several cores
    private fun develop(src: Bitmap, look: Look): Bitmap {
        val w = src.width
        val h = src.height
        val out = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888)
        val ct = look.ct
        val sat = look.sat
        val rGain = (1f + 0.25f * look.warm) * ct
        val gGain = ct
        val bGain = (1f - 0.25f * look.warm) * ct
        val t = 128f * (1f - ct)
        val amp = look.grain * 80f
        val cell = max(1, (look.size * w / 1000f).roundToInt())
        val gw = (w + cell - 1) / cell
        val gh = (h + cell - 1) / cell
        val noise = ByteArray(gw * gh)
        if (amp > 0f) {
            val r = Random()
            for (i in noise.indices) {
                noise[i] = ((r.nextInt(256) + r.nextInt(256) + r.nextInt(256)) / 3 - 128).toByte()
            }
        }
        val rows = 128
        val jobs = ArrayList<Future<*>>()
        var start = 0
        while (start < h) {
            val y0 = start
            val n = min(rows, h - y0)
            jobs.add(pixelPool.submit {
                val px = IntArray(w * n)
                src.getPixels(px, 0, w, 0, y0, w, n)
                for (j in 0 until n) {
                    val gy = ((y0 + j) / cell) * gw
                    val base = j * w
                    for (x in 0 until w) {
                        val p = px[base + x]
                        val r = (p shr 16) and 255
                        val g = (p shr 8) and 255
                        val b = p and 255
                        val l = (r * 77 + g * 150 + b * 29) shr 8
                        var rr = (l + (r - l) * sat) * rGain + t
                        var gg = (l + (g - l) * sat) * gGain + t
                        var bb = (l + (b - l) * sat) * bGain + t
                        if (amp > 0f) {
                            val ll = 0.299f * rr + 0.587f * gg + 0.114f * bb
                            val mid = (1f - abs(ll - 128f) / 170f).coerceIn(0.25f, 1f)
                            val nz = noise[gy + x / cell].toInt() * amp / 128f * mid
                            rr += nz
                            gg += nz
                            bb += nz
                        }
                        val ri = rr.coerceIn(0f, 255f).toInt()
                        val gi = gg.coerceIn(0f, 255f).toInt()
                        val bi = bb.coerceIn(0f, 255f).toInt()
                        px[base + x] = (0xFF shl 24) or (ri shl 16) or (gi shl 8) or bi
                    }
                }
                synchronized(out) { out.setPixels(px, 0, w, 0, y0, w, n) }
            })
            start += n
        }
        for (f in jobs) f.get()
        return out
    }

    private fun save(bmp: Bitmap, seq: Int, color: Boolean) {
        val prefix = if (color) "IMG_" else "MONO_"
        val name = prefix + SimpleDateFormat("yyyyMMdd_HHmmss_SSS", Locale.US).format(Date()) + ".jpg"
        val cv = ContentValues().apply {
            put(MediaStore.Images.Media.DISPLAY_NAME, name)
            put(MediaStore.Images.Media.MIME_TYPE, "image/jpeg")
            put(MediaStore.Images.Media.RELATIVE_PATH, Environment.DIRECTORY_PICTURES + "/MonoCam")
            put(MediaStore.Images.Media.IS_PENDING, 1)
        }
        val uri = contentResolver.insert(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, cv)
            ?: throw IllegalStateException("MediaStore insert failed")
        contentResolver.openOutputStream(uri)?.use { bmp.compress(Bitmap.CompressFormat.JPEG, 97, it) }
        cv.clear()
        cv.put(MediaStore.Images.Media.IS_PENDING, 0)
        contentResolver.update(uri, cv, null, null)
        val small = Bitmap.createScaledBitmap(
            bmp, 160, (160f * bmp.height / bmp.width).toInt().coerceAtLeast(1), true
        )
        runOnUiThread {
            // only replace the thumbnail if no newer shot has been taken since
            if (seq == seqCounter.get()) thumb.setImageBitmap(small)
        }
    }
}

// animated film grain drawn over the live preview
class GrainView(context: Context) : View(context) {
    var amount = 0f
    var grainSize = 1.6f

    private val tile: Bitmap = Bitmap.createBitmap(128, 128, Bitmap.Config.ARGB_8888).also { b ->
        val r = Random()
        val p = IntArray(128 * 128) {
            val g = (r.nextInt(256) + r.nextInt(256) + r.nextInt(256)) / 3
            (0xFF shl 24) or (g shl 16) or (g shl 8) or g
        }
        b.setPixels(p, 0, 128, 0, 0, 128, 128)
    }
    private val shader = BitmapShader(tile, Shader.TileMode.REPEAT, Shader.TileMode.REPEAT)
    private val paint = Paint().apply { this.shader = this@GrainView.shader; isFilterBitmap = false }
    private val rnd = Random()
    private val m = Matrix()
    private val tick = object : Runnable {
        override fun run() {
            if (amount > 0f) invalidate()
            postDelayed(this, 70)
        }
    }

    override fun onAttachedToWindow() {
        super.onAttachedToWindow()
        post(tick)
    }

    override fun onDetachedFromWindow() {
        removeCallbacks(tick)
        super.onDetachedFromWindow()
    }

    override fun onDraw(canvas: Canvas) {
        if (amount <= 0f) return
        val s = max(1f, grainSize * width / 1000f)
        m.setScale(s, s)
        m.postTranslate(rnd.nextFloat() * 128f, rnd.nextFloat() * 128f)
        shader.setLocalMatrix(m)
        paint.alpha = (amount * 90).toInt()
        canvas.drawRect(0f, 0f, width.toFloat(), height.toFloat(), paint)
    }
}
