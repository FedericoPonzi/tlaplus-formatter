plugins {
    id("java")
    id("io.ktor.plugin") version "2.3.12"
}

group = "me.fponzi"
version = "1.0-SNAPSHOT"

repositories {
    mavenCentral()
    // Add the repository for the snapshot dependency
    maven {
        url = uri("https://oss.sonatype.org/content/repositories/snapshots/")
    }
}

dependencies {
    implementation("org.lamport:tla2tools:1.7.0-SNAPSHOT")
    implementation ("commons-io:commons-io:2.16.1")
    testImplementation(platform("org.junit:junit-bom:5.10.0"))
    testImplementation("org.junit.jupiter:junit-jupiter")
    implementation("commons-cli:commons-cli:1.8.0")
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