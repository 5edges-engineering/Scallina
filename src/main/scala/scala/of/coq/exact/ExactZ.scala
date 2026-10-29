package scala.of.coq.exact

/** Constructor and pattern boundary for Rocq Z in exact-numerics output. */
object ExactZ {
  val Z0: BigInt = BigInt(0)

  def ofN(value: BigInt): BigInt = {
    require(value >= 0, "Rocq N cannot be negative")
    value
  }

  object Zpos {
    def apply(magnitude: BigInt): BigInt = ExactN.pos(magnitude)
    def unapply(value: BigInt): Option[BigInt] =
      if (value > 0) Some(value) else None
  }

  object Zneg {
    def apply(magnitude: BigInt): BigInt = -ExactN.pos(magnitude)
    def unapply(value: BigInt): Option[BigInt] =
      if (value < 0) Some(-value) else None
  }
}
