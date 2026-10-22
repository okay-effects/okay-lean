package okay.effects.bench

/** Probe/Stack.lean's four shapes on okay-simple's two implementations, each as it is: the MACHINE (the default
 * words, `okay.effects.*`) and the `Free` monad (`okay.effects.free.OnFree.*`). Drop into okay-simple's
 * `bench/src/main/scala-3/okay/effects/bench/`, then
 * `sbt -J-Xmx12g "bench/runMain okay.effects.bench.StackProbe <machine|free> <n> [state|reader|left|choose]"` */
object StackProbe {
  def time(name: String)(f: => Any): Unit = {
    val t0 = System.nanoTime(); val r = f; val t1 = System.nanoTime()
    println(f"$name: $r  ${(t1 - t0) / 1e9}%.2f s")
  }

  def main(args: Array[String]): Unit = {
    val impl = args.headOption.getOrElse("machine")
    val n = args.lift(1).map(_.toInt).getOrElse(100000000)
    val which = args.lift(2).getOrElse("all")
    val shapes: Seq[(String, () => Any)] = impl match {
      case "machine" => OnMachineShapes.shapes(n)
      case "free" => OnFreeShapes.shapes(n)
    }
    for (_ <- 1 to 5; (name, f) <- shapes if which == "all" || which == name) time(s"$impl $name $n")(f())
  }
}

object OnMachineShapes {
  import okay.effects.*
  import okay.effects.std.*

  type RS[X] = (State % Int)[X]
  def countState(i: Int): Unit ! RS = if (i == 0) pure(()) else modify[Int, RS](_ + 1).flatMap(_ => countState(i - 1))
  type RR[X] = (Reader % Int)[X]
  def countReader(i: Int, acc: Int): Int ! RR = if (i == 0) pure(acc) else ask[Int, RR].flatMap(x => countReader(i - 1, acc + x))
  def leftNested(n: Int): Int ! RS =
    (0 until n).foldLeft(pure[Int, RS](0))((p, _) => p.flatMap(a => modify[Int, RS](_ + 1).map(_ => a + 1)))
  type RC[X] = Choose[X]
  def chain(i: Int, acc: Int): Int ! RC = if (i == 0) pure(acc) else among[Int, RC](List(1)).flatMap(x => chain(i - 1, acc + x))

  def shapes(n: Int): Seq[(String, () => Any)] = Seq(
    "state" -> (() => run(state(0)(countState(n)))._1),
    "reader" -> (() => run(reader(1)(countReader(n, 0)))),
    "left" -> (() => run(state(0)(leftNested(n)))),
    "choose" -> (() => run(all(chain(n, 0))).head))
}

object OnFreeShapes {
  import okay.effects.{%, Pure}
  import okay.effects.free.OnFree.*
  import okay.effects.free.OnFree.std.*

  type RS[X] = (State % Int)[X]
  def countState(i: Int): Unit ! RS = if (i == 0) pure(()) else modify[Int, RS](_ + 1).flatMap(_ => countState(i - 1))
  type RR[X] = (Reader % Int)[X]
  def countReader(i: Int, acc: Int): Int ! RR = if (i == 0) pure(acc) else ask[Int, RR].flatMap(x => countReader(i - 1, acc + x))
  def leftNested(n: Int): Int ! RS =
    (0 until n).foldLeft(pure[Int, RS](0))((p, _) => p.flatMap(a => modify[Int, RS](_ + 1).map(_ => a + 1)))
  type RC[X] = Choose[X]
  def chain(i: Int, acc: Int): Int ! RC = if (i == 0) pure(acc) else among[Int, RC](List(1)).flatMap(x => chain(i - 1, acc + x))

  def shapes(n: Int): Seq[(String, () => Any)] = Seq(
    "state" -> (() => run(state(0)(countState(n)))._1),
    "reader" -> (() => run(reader(1)(countReader(n, 0)))),
    "left" -> (() => run(state(0)(leftNested(n)))),
    "choose" -> (() => run(all(chain(n, 0))).head))
}
