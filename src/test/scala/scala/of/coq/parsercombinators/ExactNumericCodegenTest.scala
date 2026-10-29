package scala.of.coq.parsercombinators

import org.scalatest.FunSuite
import scala.of.coq.parsercombinators.compiler.NoCurrying
import scala.of.coq.parsercombinators.compiler.Currify
import scala.of.coq.parsercombinators.compiler.ScalaOfCoq
import scala.of.coq.parsercombinators.parser.CoqParser

class ExactNumericCodegenTest extends FunSuite {
  test("CLI rejects failed source parsing rather than returning error text as generated code") {
    intercept[IllegalArgumentException] {
      scala.of.coq.Main.requireSuccessfulParse(CoqParser("Definition invalid := ."))
    }
  }

  test("optional Peano import omission is parsed explicitly") {
    val (options, files) = scala.of.coq.Main.parseCommandLineArgs(
      List("--exact-numerics", "--omit-peano-import", "Example.v"))
    assert(options('exactNumerics))
    assert(options('omitPeanoImport))
    assert(files == List("Example.v"))
  }

  test("exact numeric output can omit Peano import without changing generated definitions") {
    val source = "Definition add_nat (left right : nat) : nat := (left + right)%nat."
    val trees = CoqParser(source).get
    val default = new ScalaOfCoq(trees, Currify, exactNumerics = true)
      .createObjectFileCode("Example")
    val minimal = new ScalaOfCoq(trees, Currify, exactNumerics = true,
      omitPeanoImport = true).createObjectFileCode("Example")
    assert(default.contains("import Nat._\n"))
    assert(!minimal.contains("import Nat._\n"))
    assert(default.replace("import Nat._\n", "") == minimal)
  }

  test("Peano import omission requires exact numerics") {
    intercept[IllegalArgumentException] {
      new ScalaOfCoq(CoqParser("Definition zero : nat := 0.").get,
        Currify, omitPeanoImport = true)
    }
  }

  private def generate(source: String): String =
    new ScalaOfCoq(CoqParser(source).get, NoCurrying, exactNumerics = true).generateScalaCode

  private def generateCurried(source: String): String =
    new ScalaOfCoq(CoqParser(source).get, Currify, exactNumerics = true,
      nativeFullConstructors = true).generateScalaCode

  test("native constructor mode requires curried functions") {
    intercept[IllegalArgumentException] {
      new ScalaOfCoq(CoqParser("Definition zero : nat := 0.").get,
        NoCurrying, exactNumerics = true, nativeFullConstructors = true)
    }
  }

  test("curried functions keep partial application while constructors take all fields") {
    val output = generateCurried("""Inductive item : Type := | Pair (left right : nat).
Definition add (left right : nat) : nat := left + right.
Definition make (left right : nat) : item := Pair left right.
Definition plus_one (right : nat) : nat := add 1 right.""")
    assert(output.contains("new Pair(left, right)"))
    assert(!output.contains("Pair(left)(right)"))
    assert(output.contains("add(BigInt(\"1\"))(right)"))
  }

  test("native constructor mode rejects partial constructor application") {
    intercept[IllegalStateException] {
      generateCurried("""Inductive item : Type := | Pair (left right : nat).
Definition make_left (left : nat) : nat -> item := Pair left.""")
    }
  }

  test("Rocq unit and tt lower to Scala Unit and its value") {
    val output = generateCurried("Definition done : unit := tt.")
    assert(output.contains("def done: Unit = ()"))
  }

  test("local unit and tt names are not rewritten") {
    val output = generateCurried("""Inductive unit : Type := | tt.
Definition done : unit := tt.""")
    assert(output.contains("sealed abstract class unit"))
    assert(output.contains("case object tt"))
    assert(output.contains("def done: unit = tt"))
  }

  test("N comparison uses exact BigInt operands") {
    val output = generate("Definition n_leb (left right : N) : bool := (left <=? right)%N.")
    assert(output == "def n_leb(left: BigInt, right: BigInt): Boolean = (left <= right)")
  }

  test("large N numeral keeps every digit") {
    val output = generate("Definition max_u64 : N := 18446744073709551615.")
    assert(output == "def max_u64: BigInt = BigInt(\"18446744073709551615\")")
  }

  test("explicit nat numeral uses exact BigInt") {
    val output = generate("Definition zero_nat : nat := 0%nat.")
    assert(output == "def zero_nat: BigInt = BigInt(\"0\")")
  }

  test("unsupported numeric term scope is rejected") {
    intercept[IllegalStateException] {
      generate("Definition bad : nat := 0%unknown.")
    }
  }

  test("nat addition remains exact") {
    val output = generate("Definition add_nat (left right : nat) : nat := (left + right)%nat.")
    assert(output == "def add_nat(left: BigInt, right: BigInt): BigInt = (left + right)")
  }

  test("nat scope on a tuple keeps exact addition and the other component") {
    val output = generate("Definition counted (left right : nat) : nat * nat := (left + right, right)%nat.")
    assert(output.contains("(left + right, right)"))
  }

  test("nat scope overrides an open N scope for division") {
    intercept[IllegalStateException] {
      generate("Open Scope N_scope. Definition bad (value : nat) : nat * nat := (value / 16, value)%nat.")
    }
  }

  test("nat subtraction saturates at zero") {
    val output = generate("Definition sub_nat (left right : nat) : nat := (left - right)%nat.")
    assert(output == "def sub_nat(left: BigInt, right: BigInt): BigInt = ((left - right).max(BigInt(\"0\")))")
  }

  test("subtraction without a known natural scope is rejected") {
    intercept[IllegalStateException] {
      generate("Definition sub_unknown (left right : Z) : Z := left - right.")
    }
  }

  test("Z subtraction remains signed") {
    val output = generate("Definition sub_z (left right : Z) : Z := (left - right)%Z.")
    assert(output == "def sub_z(left: BigInt, right: BigInt): BigInt = (left - right)")
  }

  test("Z.of_N preserves arbitrary-size N exactly and rejects invalid negative inputs") {
    val output = generate("From Stdlib Require Import NArith ZArith. Definition lift (value : N) : Z := Z.of_N value.")
    assert(output == "def lift(value: BigInt): BigInt = scala.of.coq.exact.ExactZ.ofN(value)")
    val large = BigInt("184467440737095516160000000000000000000")
    assert(scala.of.coq.exact.ExactZ.ofN(large) == large)
    intercept[IllegalArgumentException] {
      scala.of.coq.exact.ExactZ.ofN(BigInt(-1))
    }
  }

  test("ZArith alone makes Z.of_N available for exact lowering") {
    val output = generate("From Stdlib Require Import ZArith. Definition lift (value : N) : Z := Z.of_N value.")
    assert(output == "def lift(value: BigInt): BigInt = scala.of.coq.exact.ExactZ.ofN(value)")
  }

  test("standard N and Z conversions use exact nonnegative boundaries") {
    val naturalOutput = generate("""From Stdlib Require Import NArith.
Definition natural_size (value : N) : N := N.size value.
Definition natural_to_nat (value : N) : nat := N.to_nat value.""")
    val integerOutput = generate("""From Stdlib Require Import ZArith.
Definition integer_of_nat (value : nat) : Z := Z.of_nat value.
Definition integer_to_nat (value : Z) : nat := Z.to_nat value.""")
    assert(naturalOutput.contains("scala.of.coq.exact.ExactN.size(value)"))
    assert(naturalOutput.contains("scala.of.coq.exact.ExactN.toNat(value)"))
    assert(integerOutput.contains("scala.of.coq.exact.ExactZ.ofNat(value)"))
    assert(integerOutput.contains("scala.of.coq.exact.ExactZ.toNat(value)"))
    val large = BigInt(1) << 128
    assert(scala.of.coq.exact.ExactN.size(BigInt(0)) == BigInt(0))
    assert(scala.of.coq.exact.ExactN.size(large) == BigInt(129))
    assert(scala.of.coq.exact.ExactN.toNat(large) == large)
    assert(scala.of.coq.exact.ExactZ.ofNat(large) == large)
    assert(scala.of.coq.exact.ExactZ.toNat(BigInt(-5)) == BigInt(0))
    assert(scala.of.coq.exact.ExactZ.toNat(large) == large)
    intercept[IllegalArgumentException] { scala.of.coq.exact.ExactN.size(BigInt(-1)) }
    intercept[IllegalArgumentException] { scala.of.coq.exact.ExactN.toNat(BigInt(-1)) }
    intercept[IllegalArgumentException] { scala.of.coq.exact.ExactZ.ofNat(BigInt(-1)) }
  }

  test("standard Z comparisons lower to exact BigInt comparisons") {
    val output = generate("""From Stdlib Require Import ZArith.
Definition integer_le (left right : Z) : bool := Z.leb left right.
Definition integer_lt (left right : Z) : bool := Z.ltb left right.""")
    assert(output.contains("def integer_le(left: BigInt, right: BigInt): Boolean = left <= right"))
    assert(output.contains("def integer_lt(left: BigInt, right: BigInt): Boolean = left < right"))
  }

  test("a scoped unary minus around Z.of_N lowers both branches exactly") {
    val output = generate("""From Stdlib Require Import Bool NArith ZArith.
Definition signed_count (negative : bool) (count : N) : Z :=
  if negative then (- Z.of_N count)%Z else Z.of_N count.""")
    assert(output.contains("if (negative) (BigInt(\"0\") - scala.of.coq.exact.ExactZ.ofN(count))"))
    assert(output.contains("else scala.of.coq.exact.ExactZ.ofN(count)"))
  }

  test("unary minus in Z scope remains exact") {
    val output = generate("Definition negate (value : Z) : Z := (- value)%Z.")
    assert(output == "def negate(value: BigInt): BigInt = (BigInt(\"0\") - value)")
  }

  test("unary minus in natural scope fails closed") {
    intercept[IllegalStateException] {
      generate("Definition invalid (value : nat) : nat := (- value)%nat.")
    }
  }

  test("N division by a positive literal uses exact BigInt") {
    val output = generate("Open Scope N_scope. Definition div16 (value : N) : N := value / 16.")
    assert(output == "def div16(value: BigInt): BigInt = value / BigInt(\"16\")")
  }

  test("N remainder by a positive literal uses exact BigInt") {
    val output = generate("Open Scope N_scope. Definition mod16 (value : N) : N := value mod 16.")
    assert(output == "def mod16(value: BigInt): BigInt = value mod BigInt(\"16\")")
  }

  test("division without a known numeric scope is rejected") {
    intercept[IllegalStateException] {
      generate("Definition div16 (value : N) : N := value / 16.")
    }
  }

  test("N division by zero is rejected until total lowering exists") {
    intercept[IllegalStateException] {
      generate("Open Scope N_scope. Definition div0 (value : N) : N := value / 0.")
    }
  }

  test("qualified Nat.div lowers total division without duplicating operands") {
    val output = generate("Definition div_nat (left right : nat) : nat := Nat.div left right.")
    assert(output.contains("scallinaNatDenominator == BigInt(\"0\")"))
    assert(output.contains("scallinaNatNumerator / scallinaNatDenominator"))
    assert(output.contains("(left, right)"))
    assert(!output.contains("Nat.div"))
  }

  test("typed wildcard binder retains function arity") {
    val output = generate("Definition max_depth (_ : nat) : nat := 16.")
    assert(output == "def max_depth(scallinaIgnoredArg1: BigInt): BigInt = BigInt(\"16\")")
  }

  test("typed wildcard binder avoids a source name collision") {
    val output = generate("Definition f (scallinaIgnoredArg1 : nat) (_ : nat) : nat := scallinaIgnoredArg1.")
    assert(output == "def f(scallinaIgnoredArg1: BigInt, scallinaIgnoredArg2: BigInt): BigInt = scallinaIgnoredArg1")
  }

  test("primed identifier is legal in generated Scala") {
    val output = generate("Definition primed (count' : nat) : nat := count'.")
    assert(output == "def primed(scallinaPrime_count_prime: BigInt): BigInt = scallinaPrime_count_prime")
  }

  test("primed pattern binder is a fresh Scala variable") {
    val output = generate("""Definition predecessor (count : nat) : nat :=
  match count with O => 0 | S count' => count' end.""")
    assert(output.contains("case scala.of.coq.exact.ExactNat.S(scallinaPrime_count_prime) => scallinaPrime_count_prime"))
  }

  test("primed name avoids a source identifier collision") {
    val output = generate("""Definition successor (scallinaPrime_count_prime count' : nat) : nat :=
  count' + scallinaPrime_count_prime.""")
    assert(output.contains("scallinaPrime_count_prime1: BigInt"))
    assert(output.contains("scallinaPrime_count_prime: BigInt"))
  }

  test("distinct primed names do not share a Scala identifier") {
    val output = generate("""Definition distinct (count'' count_prime' : nat) : nat :=
  count'' + count_prime'.""")
    assert(output.contains("scallinaPrime_count_prime_prime: BigInt"))
    assert(output.contains("scallinaPrime_count_prime_prime1: BigInt"))
  }

  test("pattern alternatives with a shared binder become separate Scala cases") {
    val output = generate("""Inductive item : Type := | A (n : nat) | B (n : nat).
Definition extract (value : item) : nat :=
  match value with | A n | B n => n end.""")
    assert(output.contains("case A(n) => n"))
    assert(output.contains("case B(n) => n"))
    assert(!output.contains("A(n) | B(n)"))
  }

  test("natural zero and successor use exact constructors in terms and patterns") {
    val output = generate("""Definition step (n : nat) : nat := S n.
Definition peel (n : nat) : nat := match n with | O => O | S previous => previous end.""")
    assert(output.contains("scala.of.coq.exact.ExactNat.S(n)"))
    assert(output.contains("case scala.of.coq.exact.ExactNat.O =>"))
    assert(output.contains("case scala.of.coq.exact.ExactNat.S(previous) =>"))
  }

  test("exact natural lowering rejects locally shadowed constructor names") {
    intercept[IllegalStateException] {
      generate("""Inductive token : Type := | O | S.
Definition choose (value : token) : token := match value with | O => S | S => O end.""")
    }
  }

  test("local record projection uses the generated field accessor") {
    val output = generate("""Record Budget := MkBudget { nodes_left : nat }.
Definition remaining (budget : Budget) : nat := nodes_left budget.""")
    assert(output.contains("def remaining(budget: Budget): BigInt = budget.nodes_left"))
    assert(!output.contains("nodes_left(budget)"))
  }

  test("ordinary unary function is not rewritten as a record projection") {
    val output = generate("""Definition increase (n : nat) : nat := S n.
Definition apply_increase (n : nat) : nat := increase n.""")
    assert(output.contains("def apply_increase(n: BigInt): BigInt = increase(n)"))
  }

  test("imported List forallb and existsb use Scala short-circuit traversal") {
    val output = generate("""From Stdlib Require Import List.
Definition all_small (values : list nat) : bool := forallb (fun n => (n <=? 5)%nat) values.
Definition any_small (values : list nat) : bool := existsb (fun n => (n <=? 5)%nat) values.""")
    assert(output.contains("values.forall((n => (n <= BigInt(\"5\"))))"))
    assert(output.contains("values.exists((n => (n <= BigInt(\"5\"))))"))
  }

  test("imported List map retains the input element type for tuple projections") {
    val output = generateCurried("""From Stdlib Require Import List.
Definition second_values (values : list (nat * nat)) : list nat := map snd values.""")
    assert(output.contains("values.map(snd)"))
  }

  test("imported Nat comparisons and maximum use exact integers") {
    val output = generateCurried("""From Stdlib Require Import PeanoNat.
Definition below (left right : nat) : bool := Nat.ltb left right.
Definition at_most (left right : nat) : bool := Nat.leb left right.
Definition same (left right : nat) : bool := Nat.eqb left right.
Definition larger (left right : nat) : nat := Nat.max left right.""")
    assert(output.contains("def below(left: BigInt)(right: BigInt): Boolean = left < right"))
    assert(output.contains("def at_most(left: BigInt)(right: BigInt): Boolean = left <= right"))
    assert(output.contains("def same(left: BigInt)(right: BigInt): Boolean = left == right"))
    assert(output.contains("def larger(left: BigInt)(right: BigInt): BigInt = left.max(right)"))
  }

  test("imported List length returns an exact natural") {
    val output = generateCurried("""From Stdlib Require Import List.
Definition size (values : list nat) : nat := length values.""")
    assert(output.contains("def size(values: List[BigInt]): BigInt = BigInt(values.length)"))
  }

  test("a local length definition is not rewritten") {
    val output = generateCurried("""From Stdlib Require Import List.
Definition length (values : list nat) : nat := 7.
Definition size (values : list nat) : nat := length values.""")
    assert(output.contains("def size(values: List[BigInt]): BigInt = length(values)"))
  }

  test("unqualified imports do not claim exact Nat or List mappings") {
    val output = generateCurried("""Require Import PeanoNat List.
Definition below (left right : nat) : bool := Nat.ltb left right.
Definition size (values : list nat) : nat := length values.""")
    assert(output.contains("Nat.ltb(left)(right)"))
    assert(output.contains("length(values)"))
  }

  test("imported N and Z constructors use exact representation adapters") {
    val output = generateCurried("""From Stdlib Require Import NArith ZArith.
Definition from_nat (value : nat) : N := N.of_nat value.
Definition from_pos (value : positive) : N := N.pos value.
Definition describe (value : Z) : nat :=
  match value with | Z0 => 0 | Zpos magnitude => 1 | Zneg magnitude => 2 end.""")
    assert(output.contains("scala.of.coq.exact.ExactN.ofNat(value)"))
    assert(output.contains("scala.of.coq.exact.ExactN.pos(value)"))
    assert(output.contains("case scala.of.coq.exact.ExactZ.Z0 =>"))
    assert(output.contains("case scala.of.coq.exact.ExactZ.Zpos(magnitude) =>"))
    assert(output.contains("case scala.of.coq.exact.ExactZ.Zneg(magnitude) =>"))
  }

  test("unqualified numeric imports do not claim the exact representation adapters") {
    val output = generateCurried("""Require Import NArith ZArith.
Definition from_nat (value : nat) : N := N.of_nat value.
Definition zero (value : Z) : nat := match value with | Z0 => 0 | _ => 1 end.""")
    assert(output.contains("N.of_nat(value)"))
    assert(output.contains("case Z0 =>"))
  }

  test("imported positive constructors use exact binary representation adapters") {
    val output = generateCurried("""From Stdlib Require Import NArith.
Definition fold_positive (value : positive) : nat :=
  match value with | xH => 1 | xO rest => 2 | xI rest => 3 end.""")
    assert(output.contains("case scala.of.coq.exact.ExactPositive.xH =>"))
    assert(output.contains("case scala.of.coq.exact.ExactPositive.xO(rest) =>"))
    assert(output.contains("case scala.of.coq.exact.ExactPositive.xI(rest) =>"))
  }

  test("imported N constructors use exact nonnegative representation adapters") {
    val output = generateCurried("""From Stdlib Require Import NArith.
Definition tag (value : N) : nat :=
  match value with | N0 => 0 | Npos magnitude => 1 end.""")
    assert(output.contains("case scala.of.coq.exact.ExactN.N0 =>"))
    assert(output.contains("case scala.of.coq.exact.ExactN.Npos(magnitude) =>"))
  }

  test("inductive type and constructor names differing only in case have distinct JVM names") {
    val output = generateCurried("""Inductive failure : Type := | Invalid | Failure (reason : failure).
Definition fail (reason : failure) : failure := Failure reason.""")
    assert(output.contains("sealed abstract class failure_type"))
    assert(output.contains("case class Failure(reason: failure_type) extends failure_type"))
    assert(output.contains("def fail(reason: failure_type): failure_type"))
  }

  test("a local map definition is not rewritten as the imported List function") {
    val output = generateCurried("""From Stdlib Require Import List.
Definition map (f : nat -> nat) (values : list nat) : list nat := values.
Definition call (values : list nat) : list nat := map (fun n => n) values.""")
    assert(output.contains("map(n => n)(values)"))
    assert(!output.contains("values.map"))
  }

  test("same-named local function is not rewritten as an imported list primitive") {
    val output = generate("""From Stdlib Require Import List.
Definition existsb (test : nat -> bool) (values : list nat) : bool := true.
Definition call (values : list nat) : bool := existsb (fun n => true) values.""")
    assert(output.contains("existsb(n => true, values)"))
    assert(!output.contains("values.exists"))
  }

  test("unqualified List import does not claim the Stdlib primitive mapping") {
    val output = generate("""Require Import List.
Definition call (values : list nat) : bool := existsb (fun n => true) values.""")
    assert(output.contains("existsb(n => true, values)"))
    assert(!output.contains("values.exists"))
  }

  test("outer list cons binds after a constructor pattern argument") {
    val output = generate("""From Stdlib Require Import List.
Import ListNotations.
Inductive cursor_item : Type := | CursorBytes (values : list nat).
Definition skip (cursor : list cursor_item) : list cursor_item :=
  match cursor with
  | CursorBytes [] :: rest => rest
  | CursorBytes (value :: values) :: rest => CursorBytes values :: rest
  | _ => cursor
  end.""")
    assert(output.contains("case CursorBytes(Nil) :: rest => rest"))
    assert(output.contains("case CursorBytes(value :: values) :: rest => CursorBytes(values) :: rest"))
    assert(!output.contains("CursorBytes(Nil :: rest)"))
  }
}
