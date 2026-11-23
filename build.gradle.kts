plugins {
    id("com.android.application") version "8.5.2"
    id("org.jetbrains.kotlin.android") version "1.9.24"
}

android {
    namespace = "com.monocam"
    compileSdk = 34

    defaultConfig {
        applicationId = "com.touristbytrade.cam"
        minSdk = 29
        targetSdk = 34
        versionCode = (System.getenv("GITHUB_RUN_NUMBER") ?: "1").toInt() + 10
        versionName = "2.0"
    }

    // sign with the private key only when it is provided (as GitHub secrets)
    val ksPass: String = System.getenv("KEYSTORE_PASSWORD") ?: ""
    val ksFile = file("keystore.p12")
    if (ksPass.isNotEmpty() && ksFile.exists()) {
        signingConfigs {
            create("tbt") {
                storeFile = ksFile
                storePassword = ksPass
                keyAlias = "tbt"
                keyPassword = ksPass
                storeType = "pkcs12"
            }
        }
        buildTypes {
            getByName("debug") {
                signingConfig = signingConfigs.getByName("tbt")
            }
        }
    }

    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_17
        targetCompatibility = JavaVersion.VERSION_17
    }
    kotlinOptions {
        jvmTarget = "17"
    }
}

dependencies {
    implementation("androidx.core:core-ktx:1.13.1")
    implementation("androidx.activity:activity-ktx:1.9.0")
    implementation("androidx.camera:camera-core:1.3.4")
    implementation("androidx.camera:camera-camera2:1.3.4")
    implementation("androidx.camera:camera-lifecycle:1.3.4")
    implementation("androidx.camera:camera-view:1.3.4")
    implementation("androidx.camera:camera-extensions:1.3.4")
}
