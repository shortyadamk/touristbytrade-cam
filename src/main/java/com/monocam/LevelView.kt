package com.monocam

import android.content.Context
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.hardware.Sensor
import android.hardware.SensorEvent
import android.hardware.SensorEventListener
import android.hardware.SensorManager
import android.view.View
import kotlin.math.abs
import kotlin.math.atan2
import kotlin.math.hypot
import kotlin.math.min
import kotlin.math.roundToInt
import kotlin.math.sqrt

private val LEVEL_YELLOW = Color.parseColor("#FFD60A")

// spirit-level overlay: a horizon line when the phone is upright, a bubble when it is held flat
class LevelView(context: Context) : View(context), SensorEventListener {

    private val sm = context.getSystemService(Context.SENSOR_SERVICE) as SensorManager
    private val sensor: Sensor? =
        sm.getDefaultSensor(Sensor.TYPE_GRAVITY) ?: sm.getDefaultSensor(Sensor.TYPE_ACCELEROMETER)

    private var on = false
    private var attached = false
    private var listening = false
    private var haveData = false
    private var gx = 0f
    private var gy = 9.8f
    private var gz = 0f

    private val d = resources.displayMetrics.density

    private val line = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE
        strokeWidth = 2f * d
        strokeCap = Paint.Cap.ROUND
        setShadowLayer(3f * d, 0f, 0f, Color.parseColor("#99000000"))
    }
    private val ref = Paint(Paint.ANTI_ALIAS_FLAG).apply {
        style = Paint.Style.STROKE
        strokeWidth = 1.5f * d
        strokeCap = Paint.Cap.ROUND
        color = Color.argb(150, 255, 255, 255)
        setShadowLayer(3f * d, 0f, 0f, Color.parseColor("#99000000"))
    }

    fun setOn(value: Boolean) {
        on = value
        visibility = if (value) View.VISIBLE else View.GONE
        refresh()
    }

    // only listen to the motion sensor while the overlay is on and the app is on screen
    private fun refresh() {
        val want = on && attached && windowVisibility == View.VISIBLE
        if (want && !listening && sensor != null) {
            sm.registerListener(this, sensor, SensorManager.SENSOR_DELAY_GAME)
            listening = true
        } else if (!want && listening) {
            sm.unregisterListener(this)
            listening = false
        }
    }

    override fun onAttachedToWindow() {
        super.onAttachedToWindow()
        attached = true
        refresh()
    }

    override fun onDetachedFromWindow() {
        attached = false
        refresh()
        super.onDetachedFromWindow()
    }

    override fun onWindowVisibilityChanged(visibility: Int) {
        super.onWindowVisibilityChanged(visibility)
        refresh()
    }

    override fun onSensorChanged(e: SensorEvent) {
        val a = if (haveData) 0.18f else 1f
        gx += (e.values[0] - gx) * a
        gy += (e.values[1] - gy) * a
        gz += (e.values[2] - gz) * a
        haveData = true
        invalidate()
    }

    override fun onAccuracyChanged(s: Sensor?, accuracy: Int) {}

    override fun onDraw(c: Canvas) {
        if (!on || !haveData) return
        val g = sqrt(gx * gx + gy * gy + gz * gz)
        if (g < 1f) return
        val cx = width / 2f
        val cy = height / 2f
        if (abs(gz) / g > 0.9f) drawBubble(c, cx, cy, g) else drawHorizon(c, cx, cy)
    }

    // phone upright: a horizon line that tilts against fixed reference marks
    private fun drawHorizon(c: Canvas, cx: Float, cy: Float) {
        val ang = Math.toDegrees(atan2(gx, gy).toDouble()).toFloat()
        val q = (ang / 90f).roundToInt() * 90f
        val level = abs(ang - q) < 1f
        val outer = min(width, height) * 0.30f
        val inner = 30f * d

        c.save()
        c.rotate(q, cx, cy)
        c.drawLine(cx - outer - 18f * d, cy, cx - outer - 6f * d, cy, ref)
        c.drawLine(cx + outer + 6f * d, cy, cx + outer + 18f * d, cy, ref)
        c.restore()

        line.color = if (level) LEVEL_YELLOW else Color.WHITE
        c.save()
        c.rotate(ang, cx, cy)
        c.drawLine(cx - outer, cy, cx - inner, cy, line)
        c.drawLine(cx + inner, cy, cx + outer, cy, line)
        c.restore()
    }

    // phone flat: a circle that slides toward the high side, match it to the fixed circle
    private fun drawBubble(c: Canvas, cx: Float, cy: Float, g: Float) {
        val level = hypot(gx, gy) / g < 0.0175f
        val reach = 90f * d
        var dx = gx / g * 260f * d
        var dy = -gy / g * 260f * d
        val m = hypot(dx, dy)
        if (m > reach) {
            dx *= reach / m
            dy *= reach / m
        }
        val r = 24f * d
        c.drawCircle(cx, cy, r, ref)
        c.drawLine(cx - r - 14f * d, cy, cx - r - 4f * d, cy, ref)
        c.drawLine(cx + r + 4f * d, cy, cx + r + 14f * d, cy, ref)
        c.drawLine(cx, cy - r - 14f * d, cx, cy - r - 4f * d, ref)
        c.drawLine(cx, cy + r + 4f * d, cx, cy + r + 14f * d, ref)

        line.color = if (level) LEVEL_YELLOW else Color.WHITE
        c.drawCircle(cx + dx, cy + dy, r, line)
    }
}
