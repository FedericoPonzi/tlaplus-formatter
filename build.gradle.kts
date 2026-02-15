plugins {
    id("java")
    id("io.ktor.plugin") version "2.3.12"
    id("com.github.spotbugs") version "6.0.7"
    jacoco
}

group = "me.fponzi"
version = "0.2.1"

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
    // TODO: Replace with a stable release when available:
    implementation("com.github.FedericoPonzi:tlaplus:0d86214464")
    implementation("commons-io:commons-io:2.16.1")
    testImplementation("com.github.FedericoPonzi:tlaplus-smith:f5a70e21d1") {
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
    implementation("ch.qos.logback:logback-classic:1.5.28")

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
    finalizedBy(tasks.jacocoTestReport)
    System.getProperty("TLA-Library")?.let { systemProperty("TLA-Library", it) }
}

tasks.jacocoTestReport {
    dependsOn(tasks.test)
    reports {
        xml.required.set(true)
        html.required.set(true)
    }
}

tasks.register<Test>("semanticPreservationTest") {
    useJUnitPlatform()
    filter {
        includeTestsMatching("me.fponzi.tlaplusformatter.TlaPlusExamplesSemanticPreservationTest")
    }
    systemProperties(System.getProperties().filter { (k, _) -> k.toString().startsWith("tlaplus.") }
        .map { (k, v) -> k.toString() to v.toString() }.toMap())
    System.getProperty("TLA-Library")?.let { systemProperty("TLA-Library", it) }
}

tasks.register("generateVersionProperties") {
    val outputDir = layout.buildDirectory.dir("generated-resources/version")
    outputs.dir(outputDir)
    doLast {
        val dir = outputDir.get().asFile
        dir.mkdirs()
        val commitId = try {
            providers.exec {
                commandLine("git", "rev-parse", "--short", "HEAD")
            }.standardOutput.asText.get().trim()
        } catch (e: Exception) {
            "unknown"
        }
        File(dir, "version.properties").writeText(
            "version=${project.version}\ngit.commit=$commitId\n"
        )
    }
}

sourceSets {
    getByName("main") {
        resources {
            srcDir(layout.buildDirectory.dir("generated-resources/version"))
        }
    }
}

tasks.named("processResources") {
    dependsOn("generateVersionProperties")
}

application {
    mainClass = "me.fponzi.tlaplusformatter.Main"
}

ktor {
    fatJar {
        archiveFileName.set("tlaplus-formatter.jar")
    }
}

tasks.register<Jar>("buildWebJar") {
    description = "Build a fat JAR for CheerpJ (excludes classes incompatible with Java 11)"
    dependsOn("buildFatJar")
    archiveFileName.set("tlaplus-formatter-web.jar")
    destinationDirectory.set(layout.buildDirectory.dir("libs"))
    // Use provider to ensure lazy evaluation after buildFatJar completes
    from(provider { zipTree(layout.buildDirectory.file("libs/tlaplus-formatter.jar")) }) {
        exclude("META-INF/versions/**")
        exclude("**/module-info.class")
    }
    manifest {
        attributes("Main-Class" to "me.fponzi.tlaplusformatter.Main")
    }
}

spotbugs {
    ignoreFailures.set(false)
    showStackTraces.set(true)
    effort.set(com.github.spotbugs.snom.Effort.DEFAULT)
    reportLevel.set(com.github.spotbugs.snom.Confidence.DEFAULT)
    excludeFilter.set(file("spotbugs-exclude.xml"))
}

tasks.withType<com.github.spotbugs.snom.SpotBugsTask>().configureEach {
    reports.create("html") {
        required.set(true)
    }
}
