plugins {
    id("java")
    id("io.ktor.plugin") version "2.3.12"
}

group = "me.fponzi"
version = "1.0-SNAPSHOT"

java {
    sourceCompatibility = JavaVersion.VERSION_11
    targetCompatibility = JavaVersion.VERSION_11
}

repositories {
    mavenLocal()
    mavenCentral()
    // Add the repository for the snapshot dependency
    maven {
        url = uri("https://oss.sonatype.org/content/repositories/snapshots/")
    }
    maven {
        url = uri("https://jitpack.io")
    }
}

dependencies {
    implementation("org.lamport:tla2tools:1.8.0-SNAPSHOT")
    implementation("commons-io:commons-io:2.16.1")
    testImplementation("com.github.FedericoPonzi:tlaplus-smith:17e32e0915") {
        isChanging = true
    }

    testImplementation(platform("org.junit:junit-bom:5.10.0"))
    testImplementation("org.junit.jupiter:junit-jupiter")
    testImplementation("org.mockito:mockito-core:5.7.0")
    testImplementation("org.mockito:mockito-junit-jupiter:5.7.0")
    testImplementation("net.jqwik:jqwik:1.8.0")
    implementation("commons-cli:commons-cli:1.8.0")

    // Logging
    implementation("org.slf4j:slf4j-api:2.0.7")
    implementation("ch.qos.logback:logback-classic:1.5.6")

    implementation("com.opencastsoftware:prettier4j:0.3.2")
}

sourceSets {
    getByName("test") {
        resources {
            srcDir("src/test/resources")
        }
    }
}

// Configure the copy task to handle duplicates
tasks.withType<Copy> {
    duplicatesStrategy = DuplicatesStrategy.EXCLUDE // or use DuplicatesStrategy.INCLUDE, DuplicatesStrategy.WARN, etc.
}

tasks.test {
    useJUnitPlatform()
}

application {
    mainClass = "me.fponzi.tlaplusformatter.Main"
}

ktor {
    fatJar {
        archiveFileName.set("tlaplus-formatter.jar")
    }
}