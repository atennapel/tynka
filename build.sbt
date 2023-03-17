val scala3Version = "3.2.2"

lazy val root = project
  .in(file("."))
  .settings(
    name := "tynka",
    version := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,
    libraryDependencies += "com.github.j-mie6" %% "parsley" % "3.3.10",
    libraryDependencies += "org.ow2.asm" % "asm" % "9.4",
    libraryDependencies += "org.ow2.asm" % "asm-commons" % "9.4",
    libraryDependencies += "org.scalameta" %% "munit" % "0.7.29" % Test,
    scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
      "-indent",
      "-new-syntax",
      "-print-lines",
      "-unchecked",
      "-Ykind-projector",
      "-Xfatal-warnings",
      "-Xmigration"
    )
  )
