import Extra.Fin.Coding

namespace Fin

class Enum (α : Type _) where
  size : Nat
  enum : Fin size → α
  find : α → Fin size
  find_eq_iff_enum_eq : enum i = x ↔ find x = i

def Enum.ofEquiv (e : Equiv (Fin n) α) : Enum α where
  size := n
  enum := e.fwd
  find := e.rev
  find_eq_iff_enum_eq := e.fwd_eq_iff_rev_eq

def Enum.toEquiv (α) [Enum α] : Equiv (Fin (Enum.size α)) α where
  fwd := Enum.enum
  rev := Enum.find
  fwd_eq_iff_rev_eq := Enum.find_eq_iff_enum_eq

instance : Enum Empty := .ofEquiv equivEmpty

instance : Enum PUnit := .ofEquiv equivPUnit

instance : Enum Unit := .ofEquiv equivUnit

instance : Enum Bool := .ofEquiv equivBool

instance (n) : Enum (Fin n) := .ofEquiv .id

instance (α) [Enum α] : Enum (Option α) :=
  .ofEquiv <| .comp (Option.equiv (Enum.toEquiv α)) (equivOption (Enum.size α))

instance (α β) [Enum α] [Enum β] : Enum (Sum α β) :=
  .ofEquiv <| .comp (Sum.equiv (Enum.toEquiv α) (Enum.toEquiv β)) (equivSum (Enum.size α) (Enum.size β))

instance (α β) [Enum α] [Enum β] : Enum (Prod α β) :=
  .ofEquiv <| .comp (Prod.equiv (Enum.toEquiv α) (Enum.toEquiv β)) (equivProd (Enum.size α) (Enum.size β))

instance (β : α → Type _) [Enum α] [(x : α) → Enum (β x)] : Enum (Sigma β) :=
  .ofEquiv <| .comp (Sigma.equiv (Enum.toEquiv α) (fun x => Enum.toEquiv (β (Enum.enum x)))) (equivSigma (fun x => Enum.size (β (Enum.enum x))))

instance (β : α → Type _) [Enum α] [(x : α) → Enum (β x)] : Enum ((x : α) → β x) :=
  .ofEquiv <| .comp (Fun.equiv (Enum.toEquiv α) (fun x => Enum.toEquiv (β (Enum.enum x)))) (equivPi (fun x => Enum.size (β (Enum.enum x))))

instance (p : α → Prop) [DecidablePred p] [Enum α] : Enum { x // p x} :=
  .ofEquiv <| .comp (Subtype.equiv (Enum.toEquiv α) spec) (equivSubtype (fun i => p (Enum.enum i)))
where
  spec := by intros; simp [Enum.toEquiv]

instance (s : Setoid α) [DecidableRel s.r] [Enum α] : Enum (Quotient s) :=
  .ofEquiv <| .comp (Quotient.equiv (Enum.toEquiv α) spec) (equivQuotient (s.map fun i => Enum.enum i))
where
  spec := by intros; simp [Enum.toEquiv, HasEquiv.Equiv, Setoid.map]
