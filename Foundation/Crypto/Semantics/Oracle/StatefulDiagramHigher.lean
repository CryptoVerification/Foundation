import Foundation.Crypto.Semantics.Oracle.StatefulDiagramAnalysisTransport

/-! Three bounded higher diagrams for the checked stateful exchange language:
involution (two swaps), braid (three swaps on each boundary), and disjoint
swaps (two each). They are proof data, not an arbitrary-parallel-path generator.
Global completeness of the higher presentation is not claimed here. -/
namespace CryptoOracle.StatefulDiagram
variable {Slot Op : Type} [DecidableEq Slot]

def Exchange.whisker (signature : Op → Interface Slot) : {one two : List Op} →
    (certificate : Exchange signature one two) → (past future : List Op) →
    Exchange signature (past ++ one ++ future) (past ++ two ++ future)
  | _, _, .refl _, _, _ => .refl _
  | _, _, .swap before after first second accepted, past, future => by
      simpa only [List.append_assoc] using
        Exchange.swap (past ++ before) (after ++ future) first second accepted
  | _, _, .symm certificate, past, future => (certificate.whisker signature past future).symm
  | _, _, .trans first second, past, future =>
      (first.whisker signature past future).trans (second.whisker signature past future)

def Exchange.swapCount (signature : Op → Interface Slot) : {one two : List Op} → Exchange signature one two → Nat
  | _, _, .refl _ => 0
  | _, _, .swap _ _ _ _ _ => 1
  | _, _, .symm certificate => certificate.swapCount signature
  | _, _, .trans first second => first.swapCount signature + second.swapCount signature

def braidLeft (signature : Op → Interface Slot) (a b c : Op)
    (ab : checkExchange signature a b = true) (ac : checkExchange signature a c = true)
    (bc : checkExchange signature b c = true) : Exchange signature [a, b, c] [c, b, a] :=
  (Exchange.swap [] [c] a b ab).trans ((Exchange.swap [b] [] a c ac).trans (Exchange.swap [] [a] b c bc))

def braidRight (signature : Op → Interface Slot) (a b c : Op)
    (ab : checkExchange signature a b = true) (ac : checkExchange signature a c = true)
    (bc : checkExchange signature b c = true) : Exchange signature [a, b, c] [c, b, a] :=
  (Exchange.swap [a] [] b c bc).trans ((Exchange.swap [] [b] a c ac).trans (Exchange.swap [c] [] a b ab))

def swapTwice (signature : Op → Interface Slot) (a b : Op)
    (ab : checkExchange signature a b = true) (ba : checkExchange signature b a = true) :
    Exchange signature [a, b] [a, b] :=
  (Exchange.swap [] [] a b ab).trans (Exchange.swap [] [] b a ba)

def farLeft (signature : Op → Interface Slot) (a b c d : Op)
    (ab : checkExchange signature a b = true) (cd : checkExchange signature c d = true) :
    Exchange signature [a, b, c, d] [b, a, d, c] :=
  (Exchange.swap [] [c, d] a b ab).trans (Exchange.swap [b, a] [] c d cd)

def farRight (signature : Op → Interface Slot) (a b c d : Op)
    (ab : checkExchange signature a b = true) (cd : checkExchange signature c d = true) :
    Exchange signature [a, b, c, d] [b, a, d, c] :=
  (Exchange.swap [a, b] [] c d cd).trans (Exchange.swap [] [d, c] a b ab)


/-- Explicit bounded higher generators and their pasting/context closure.
These declarations do not assert completeness for arbitrary exchange paths. -/
inductive ExchangeHigher (signature : Op → Interface Slot) : {one two : List Op} →
    Exchange signature one two → Exchange signature one two → Type where
  | refl {one two} (certificate : Exchange signature one two) : ExchangeHigher signature certificate certificate
  | involution (a b : Op) (ab : checkExchange signature a b = true) (ba : checkExchange signature b a = true) :
      ExchangeHigher signature (swapTwice signature a b ab ba) (.refl [a, b])
  | braid (a b c : Op) (ab : checkExchange signature a b = true) (ac : checkExchange signature a c = true)
      (bc : checkExchange signature b c = true) :
      ExchangeHigher signature (braidLeft signature a b c ab ac bc) (braidRight signature a b c ab ac bc)
  | far (a b c d : Op) (ab : checkExchange signature a b = true) (cd : checkExchange signature c d = true) :
      ExchangeHigher signature (farLeft signature a b c d ab cd) (farRight signature a b c d ab cd)
  | symm {one two} {first second : Exchange signature one two} :
      ExchangeHigher signature first second → ExchangeHigher signature second first
  | trans {one two} {first second third : Exchange signature one two} :
      ExchangeHigher signature first second → ExchangeHigher signature second third → ExchangeHigher signature first third
  | comp {one two three} {first first' : Exchange signature one two} {second second' : Exchange signature two three} :
      ExchangeHigher signature first first' → ExchangeHigher signature second second' →
        ExchangeHigher signature (.trans first second) (.trans first' second')
  | whisker {one two} {first second : Exchange signature one two} (past future : List Op) :
      ExchangeHigher signature first second →
        ExchangeHigher signature (first.whisker signature past future) (second.whisker signature past future)

theorem braidLeft_count (signature : Op → Interface Slot) (a b c : Op)
    (ab : checkExchange signature a b = true) (ac : checkExchange signature a c = true)
    (bc : checkExchange signature b c = true) : (braidLeft signature a b c ab ac bc).swapCount signature = 3 := rfl

theorem braidRight_count (signature : Op → Interface Slot) (a b c : Op)
    (ab : checkExchange signature a b = true) (ac : checkExchange signature a c = true)
    (bc : checkExchange signature b c = true) : (braidRight signature a b c ab ac bc).swapCount signature = 3 := rfl

theorem swapTwice_count (signature : Op → Interface Slot) (a b : Op)
    (ab : checkExchange signature a b = true) (ba : checkExchange signature b a = true) :
    (swapTwice signature a b ab ba).swapCount signature = 2 := rfl

theorem farLeft_count (signature : Op → Interface Slot) (a b c d : Op)
    (ab : checkExchange signature a b = true) (cd : checkExchange signature c d = true) :
    (farLeft signature a b c d ab cd).swapCount signature = 2 := rfl

theorem farRight_count (signature : Op → Interface Slot) (a b c d : Op)
    (ab : checkExchange signature a b = true) (cd : checkExchange signature c d = true) :
    (farRight signature a b c d ab cd).swapCount signature = 2 := rfl

end CryptoOracle.StatefulDiagram
