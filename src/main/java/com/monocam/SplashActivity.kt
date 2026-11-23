package com.monocam

import android.content.Intent
import android.graphics.BitmapFactory
import android.graphics.Color
import android.os.Bundle
import android.util.Base64
import android.view.Gravity
import android.view.ViewGroup
import android.widget.FrameLayout
import android.widget.ImageView
import androidx.activity.ComponentActivity

class SplashActivity : ComponentActivity() {

    private val go = Runnable {
        startActivity(Intent(this, MainActivity::class.java))
        finish()
        overridePendingTransition(android.R.anim.fade_in, android.R.anim.fade_out)
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        window.statusBarColor = Color.BLACK
        window.navigationBarColor = Color.BLACK

        val root = FrameLayout(this)
        root.setBackgroundColor(Color.BLACK)

        val img = ImageView(this)
        try {
            val bytes = Base64.decode(LogoData.PNG, Base64.DEFAULT)
            img.setImageBitmap(BitmapFactory.decodeByteArray(bytes, 0, bytes.size))
        } catch (e: Exception) {
        }
        img.adjustViewBounds = true
        img.scaleType = ImageView.ScaleType.FIT_CENTER
        img.alpha = 0f
        val w = (resources.displayMetrics.widthPixels * 0.7f).toInt()
        root.addView(
            img,
            FrameLayout.LayoutParams(w, ViewGroup.LayoutParams.WRAP_CONTENT, Gravity.CENTER)
        )
        setContentView(root)

        img.animate().alpha(1f).setDuration(150).start()
    }

    override fun onResume() {
        super.onResume()
        window.decorView.postDelayed(go, 700)
    }

    override fun onPause() {
        super.onPause()
        window.decorView.removeCallbacks(go)
    }
}
