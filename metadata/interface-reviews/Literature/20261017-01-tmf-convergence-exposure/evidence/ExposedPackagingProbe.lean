module

/- Mechanism-only probe. It deliberately compares declarations with and without
   extracted public proof helpers; none is proposed as a production interface. -/

@[expose] section
namespace KIP126.Literature.ExposedPackagingProbe

private theorem privateReflexivity (n : Nat) : n = n := rfl

public def directAtomicProof (n : Nat) : {m : Nat // m = n} :=
  let hn : n = n := Eq.refl n
  ⟨n, hn⟩

public def directAtomicTrans (n : Nat) : {m : Nat // m = n} :=
  let hn : n = n := Eq.refl n
  let ht : n = n := Eq.trans hn hn
  ⟨n, ht⟩

public def nestedByProof (n : Nat) : {m : Nat // m = n} :=
  ⟨n, by rfl⟩

public def privateViaBy (n : Nat) : {m : Nat // m = n} :=
  ⟨n, by exact privateReflexivity n⟩

public def compositeTerm (n : Nat) : {m : Nat // m = n} :=
  ⟨n, Eq.trans (Eq.refl n) (Eq.refl n)⟩

/--
error: Unknown identifier `privateReflexivity`

Note: A private declaration `privateReflexivity` (from the current module) exists but would need to be public to access here.
-/
#guard_msgs in
public def privateDirect (n : Nat) : {m : Nat // m = n} :=
  ⟨n, privateReflexivity n⟩

/- The same failure occurs with `(show n = n from privateReflexivity n)`.
Expected type Prop does not change name-resolution visibility.
-/

#print directAtomicProof
#print directAtomicTrans
#print nestedByProof
#print privateViaBy
#print compositeTerm

end KIP126.Literature.ExposedPackagingProbe
