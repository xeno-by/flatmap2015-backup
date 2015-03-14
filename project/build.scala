import sbt._
import Keys._

object build extends Build {
  lazy val sharedSettings = Defaults.defaultSettings ++ Seq(
    scalaVersion := "2.11.6",
    version := "0.1.0-SNAPSHOT",
    organization := "org.scalameta",
    resolvers += Resolver.sonatypeRepo("snapshots"),
    resolvers += Resolver.sonatypeRepo("releases"),
    scalacOptions ++= Seq("-deprecation", "-feature"),
    parallelExecution in Test := false, // hello, reflection sync!!
    logBuffered := false
  )

  lazy val core = Project(
    id   = "core",
    base = file("core")
  ) settings (
    sharedSettings : _*
  ) settings (
    addCompilerPlugin("org.scalamacros" % "macrotracker" % "0.1.0" cross CrossVersion.full),
    incOptions := incOptions.value.withNameHashing(true)
  ) dependsOn (macros)

  lazy val macros = Project(
    id   = "macros",
    base = file("macros")
  ) settings (
    sharedSettings: _*
  ) settings (
    libraryDependencies <+= (scalaVersion)("org.scala-lang" % "scala-reflect" % _),
    libraryDependencies <<= (libraryDependencies, scalaVersion) { (libraryDependencies, scalaVersion) =>
      CrossVersion.partialVersion(scalaVersion) match {
        // if Scala 2.11+ is used, quasiquotes are available in the standard distribution
        case Some((2, scalaMajor)) if scalaMajor >= 11 =>
          libraryDependencies
        // in Scala 2.10, quasiquotes are provided by macro paradise
        case Some((2, 10)) =>
          libraryDependencies ++ Seq(
            compilerPlugin("org.scalamacros" % "paradise" % "2.1.0-M5" cross CrossVersion.full),
            "org.scalamacros" %% "quasiquotes" % "2.1.0-M5" cross CrossVersion.binary)
        case _ =>
          libraryDependencies
      }
    }
  )
}
