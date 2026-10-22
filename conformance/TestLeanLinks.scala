package okay.rust

import java.nio.file.{Files, Path, Paths}
import okay.foreign.{ForeignWorker, WireConformance}

/**
 * okay-lean's worker against okay's ONE conformance body (`WireConformance`), over a child process's pipes and IN THIS
 * PROCESS through FFM. Lives in okay-lean (`conformance/`); run from okay's `okay-rust` JVM tests, which have FFM:
 *
 *   okay-lean$ lake build lean-worker && scripts/ffm-worker.sh
 *   okay$ cp ../okay-lean/conformance/TestLeanLinks.scala okay-rust/.jvm/src/test/scala/okay/rust/
 *   okay$ sbt "set every Test / testOptions := Seq(Tests.Argument(TestFrameworks.MUnit, \"--include-tags=Live\"))" \
 *             "okayRustJVM/testOnly okay.rust.TestLean*"
 *
 * The conformance tests are tagged `Live`, which okay's build excludes by default: hence the `set`.
 *
 * The worker's directory is OKAY_LEAN, by default ~/work/my/okay-lean. Programs as data only: no direct style, no
 * streams (they are a muxed worker's), so those tests are skipped as for Haskell.
 */
object LeanWorker:
  val dir: Path = Paths.get(sys.env.getOrElse("OKAY_LEAN", sys.props("user.home") + "/work/my/okay-lean"))
  val binary: Path = dir.resolve(".lake/build/bin/lean-worker")
  val library: Path = dir.resolve(".lake/build/lib").resolve(NativeLib.fileName("okay-lean-worker"))

/** (Lean, pipes), JSON */
class TestLeanPipes extends WireConformance:
  override def munitIgnore: Boolean = !Files.isExecutable(LeanWorker.binary)
  override def direct: Boolean = false
  lazy val engine: ForeignWorker = ForeignWorker.speaking(Seq(LeanWorker.binary.toString))
  override def afterAll(): Unit = if !munitIgnore then engine.close()

  test("the hello: a Lean worker, on JSON lines") {
    assertEquals(engine.pythonVersion, "lean")
    assertEquals(engine.wire, "json/none")
  }

/** (Lean, FFM): the same worker in this process, a library of okay's C ABI */
class TestLeanFfm extends WireConformance:
  override def munitIgnore: Boolean = !Files.exists(LeanWorker.library)
  override def direct: Boolean = false
  lazy val engine: ForeignWorker = ForeignWorker.inProcess(LeanWorker.library)
  override def afterAll(): Unit = if !munitIgnore then engine.close()

  test("in-process: a Lean worker, on JSON, no compression") {
    assertEquals(engine.pythonVersion, "lean")
    assert(engine.wire.startsWith("json/none"), engine.wire)
  }
