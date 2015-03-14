resolvers += "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots"

lazy val root = (project in file(".")).
  settings (
    name := "demo",
    scalaVersion := "2.11.6"
  ) dependsOn(rules) enablePlugins(obeyplugin)
