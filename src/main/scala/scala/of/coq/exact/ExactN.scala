package scala.of.coq.exact

/** Representation boundary for Rocq N and positive values in exact-numerics output. */
object ExactN {
  val N0: BigInt = BigInt(0)

  object Npos {
    def apply(value: BigInt): BigInt = pos(value)

    def unapply(value: BigInt): Option[BigInt] =
      if (value > 0) Some(value) else None
  }

  def ofNat(value: BigInt): BigInt = {
    require(value >= 0, "Rocq nat cannot be negative")
    value
  }

  def toNat(value: BigInt): BigInt = {
    require(value >= 0, "Rocq N cannot be negative")
    value
  }

  def size(value: BigInt): BigInt = BigInt(toNat(value).bitLength)

  def pos(value: BigInt): BigInt = {
    require(value > 0, "Rocq positive must be greater than zero")
    value
  }
}
