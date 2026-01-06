plugins {
    java
    application
}

repositories {
    mavenCentral()
}

dependencies {
    implementation("com.amazon.ion:ion-java:1.11.9")
}

java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(17))
    }
}

application {
    mainClass.set("com.strata.test.GenerateTestData")
}