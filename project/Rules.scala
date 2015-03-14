import sbt._
import Keys._

object Rules extends Build {
  lazy val rules = (project in file("project/rules")).
    settings (
      name := "rules",
      scalaVersion := "2.11.6",
      resolvers += "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots",
      libraryDependencies += "com.github.mdemarne" % "model" % "0.1.0-SNAPSHOT" cross CrossVersion.full
  )
}