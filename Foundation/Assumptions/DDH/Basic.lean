/-- Parameters sufficient to state DDH challenge syntax, without group laws. -/
structure DDHParameters where
  Element : Type
  Scalar : Type
  generator : Element
  power : Element → Scalar → Element
  mulScalar : Scalar → Scalar → Scalar
  /-- Element multiplication as syntax only; no algebraic laws are assumed. -/
  mul : Element → Element → Element
