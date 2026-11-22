import Formalism.LocalToGlobal.CharacterGerms.Bundle0026
import Formalism.LocalToGlobal.CharacterGerms.Bundle0024
import Formalism.LocalToGlobal.CharacterGerms.Bundle0016
import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqSum2

-- bundled from Formalism.LocalToGlobal.CharacterGerms.CanonicalGaugeFirstPartialLawEq
section
noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace CocycleIdentity

open PartialDerivEval

section Slice

variable {C : Type} [Field C] {V : VF C} {dd : ℕ}

def lo (ν : Fin 2 × Fin dd →₀ ℕ) : Fin 3 × Fin dd →₀ ℕ :=
  ν.mapDomain fun p => (Fin.castSucc p.1, p.2)

def ZOne (F : PS C 3 dd) : Prop :=
  ∀ α : Fin 3 × Fin dd →₀ ℕ, (∀ k, α ((2 : Fin 3), k) = 0) → coeff α F = if α = 0 then 1 else 0

def FrobZ (V : VF C) (F : PS C 3 dd) : Prop :=
  ∀ α : Fin 3 × Fin dd →₀ ℕ, (∃ k, ¬ V.l ∣ α ((2 : Fin 3), k)) → V.MM (coeff α F)

end Slice

section Geo

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

def lift (a : Pt C 2 dd) : Pt C 3 dd := fun j => ev (n := 3) ![pt C dd 0, pt C dd 1] (a j)

def uAt (a : Pt C 2 dd) : PS C 3 dd := ev ![lift a, pt C dd 2] Y.u2

abbrev S3 : Pt C 3 dd := addOf Y.B.G.F (pt C dd 0) (pt C dd 1)

abbrev L3 : Pt C 3 dd := comp1 (Y.nmul V.l) (pt C dd 2)

abbrev hx (a b : Pt C 3 dd) : PS C 3 dd := ev ![a, b] Y.h

abbrev G1 : PS C 3 dd := hx Y (pt C dd 0) (pt C dd 2) + hx Y (pt C dd 1) (pt C dd 2) - hx Y (S3 Y) (pt C dd 2)

end Geo

section Closed

def XSliceSt : Prop :=
  UnitSeriesFrobenius → ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (a : Pt C 2 dd), (∀ j, constantCoeff (a j) = 0) → (∀ j, IntS V (a j)) →
    IntS V (uAt Y a) ∧ ZOne (uAt Y a) ∧ FrobZ V (uAt Y a) ∧
      ∀ (i : Fin dd) (ν : Fin 2 × Fin dd →₀ ℕ),
        coeff (lo ν + Finsupp.single ((2 : Fin 3), i) V.l) (uAt Y a) = coeff ν (ev ![a] (Y.fS i))

def PhLSliceSt : Prop :=
  LMulFrobFBSt → ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (i : Fin dd),
    IntS V (ev ![pt C dd 0, pt C dd 1, L3 Y] Y.B.ph1) ∧ ZOne (ev ![pt C dd 0, pt C dd 1, L3 Y] Y.B.ph1) ∧
      FrobZ V (ev ![pt C dd 0, pt C dd 1, L3 Y] Y.B.ph1) ∧
      ∀ ν : Fin 2 × Fin dd →₀ ℕ,
        V.MM (coeff (lo ν + Finsupp.single ((2 : Fin 3), i) V.l) (ev ![pt C dd 0, pt C dd 1, L3 Y] Y.B.ph1) -
          coeff ν (∑ j, Y.cS j * MvPowerSeries.C (Y.V1 j i)))

def PhPowSliceSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (i : Fin dd),
    IntS V (Y.B.ph1 ^ V.l) ∧ ZOne (Y.B.ph1 ^ V.l) ∧ FrobZ V (Y.B.ph1 ^ V.l) ∧
      ∀ ν : Fin 2 × Fin dd →₀ ℕ,
        V.MM (coeff (lo ν + Finsupp.single ((2 : Fin 3), i) V.l) (Y.B.ph1 ^ V.l) - coeff ν (Y.cS i ^ V.l))

end Closed

end CocycleIdentity

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ConstantZeroMultiplicationEval
section
set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UnitSeriesFrobeniusLemmas

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries PartialDerivEval LMulP

section Gen

variable {C : Type} [Field C] {V : VF C}

end Gen

section Main

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {d : ℕ}
  (Y : FBChart C V O d)

def Lz : Pt C 2 d := comp1 (Y.nmul V.l) (pt C d 1)

theorem hz1 : Z0 (![pt C d 1] : Fin 1 → Pt C 2 d) := z0_1 _ fun i => z0_pt 1 i

def EL : Fin 2 → Pt C 2 d := ![pt C d 0, Lz Y]

def Mz (j k : Fin d) : PS C 2 d := ev (n := 2) ![pt C d 1, 0] (pderiv C ((1 : Fin 2), k) (Y.B.G.F j))

def Gk (k : Fin d) : PS C 2 d :=
  (∑ j, Mz Y j k * pderiv C ((1 : Fin 2), j) Y.h) + ev (n := 2) ![pt C d 0] (Y.sgP (Pi.single k 1))

def HH : PS C 2 d := ev (EL Y) Y.h - MvPowerSeries.C (V.l : C) * Y.h

end Main

end UnitSeriesFrobeniusLemmas

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.PderivSubGOff
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Chain

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem chain_aeval {σ τ : Type} [Fintype σ] (S : MvPolynomial σ C →ₐ[C] MvPolynomial τ C) (ℓ : τ) (p : MvPolynomial σ C) :
    pderiv ℓ (S p) = ∑ y, S (pderiv y p) * pderiv ℓ (S (X y)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [MvPolynomial.algHom_C, MvPolynomial.pderiv_C]
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have key : ∀ y, S (pderiv y (p * X i)) = (if i = y then S p else 0) + S (X i) * S (pderiv y p) := by
      intro y
      rw [Derivation.leibniz, pderiv_X]
      by_cases h : i = y
      · subst h
        simp
      · simp [Pi.single_apply, h]
    conv_lhs => rw [map_mul S p (X i), Derivation.leibniz, hp]
    simp only [key, smul_eq_mul, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
    try ring

theorem pderiv_subG_off {p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C} {ℓ : Letter T r n}
    (h : ∀ z, ℓ ≠ lam r tau plc z) : pderiv ℓ (subG r tau gm plc p) = 0 := by
  rw [chain_aeval]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hX : pderiv ℓ (subG r tau gm plc (X y)) = 0 := by
    unfold subG
    rw [MvPolynomial.aeval_X, map_sum]
    refine Finset.sum_eq_zero fun col _ => ?_
    rw [Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero, MvPolynomial.pderiv_X]
    have hne : (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n) ≠ ℓ := by
      intro heq
      apply h (((eW r tau N) y).1, col)
      rw [← heq]
      rfl
    simp [Pi.single_apply, hne]
  rw [hX, mul_zero]

private theorem lam_injective_of_tau_injective (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (z z' : AA r tau N × Fin 2) (h : lam r tau plc z = lam r tau plc z') : z = z' := by
  obtain ⟨⟨n1, o1, s1, i1⟩, c1⟩ := z
  obtain ⟨⟨n2, o2, s2, i2⟩, c2⟩ := z'
  injection h with h0 h3
  have h1 : tau o1 s1 = tau o2 s2 := h0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (@inj (o1, s1) (o2, s2) h1)
  have h4 : (i1, plc (n1, c1)) = (i2, plc (n2, c2)) := eq_of_heq h3
  obtain ⟨rfl, h5⟩ := Prod.mk.inj h4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (plc.injective h5)
  rfl

private theorem pderiv_lam_subG_X_eq_ite (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (α0 : AA r tau N) (col0 : Fin 2) (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) :
    pderiv (lam r tau plc (α0, col0)) (subG r tau gm plc (X y)) =
      if (eW r tau N y).1 = α0 then MvPolynomial.C (gm y.2.1 y.2.2.2.1 col0 y.2.2.1) else 0 := by
  unfold subG
  rw [MvPolynomial.aeval_X, map_sum]
  have key : ∀ col : Fin 2, pderiv (lam r tau plc (α0, col0))
      (MvPolynomial.C (gm y.2.1 y.2.2.2.1 col y.2.2.1) *
        MvPolynomial.X (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n)) =
      if ((eW r tau N y).1, col) = (α0, col0) then MvPolynomial.C (gm y.2.1 y.2.2.2.1 col y.2.2.1) else 0 := by
    intro col
    rw [Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero, MvPolynomial.pderiv_X]
    have e1 : (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n) =
        lam r tau plc ((eW r tau N y).1, col) := rfl
    rw [e1, Pi.single_apply]
    by_cases hz : ((eW r tau N y).1, col) = (α0, col0)
    · rw [if_pos (congrArg (lam r tau plc) hz), if_pos hz, smul_eq_mul, mul_one]
    · rw [if_neg (fun h' => hz (lam_injective_of_tau_injective plc inj _ _ h')), if_neg hz, smul_zero]
  simp only [key]
  by_cases ha : (eW r tau N y).1 = α0
  · simp [ha]
  · simp [ha]

theorem pderiv_subG_lam (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α0 : AA r tau N) (col0 : Fin 2)
    (p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    pderiv (lam r tau plc (α0, col0)) (subG r tau gm plc p) =
      ∑ g, MvPolynomial.C (Gm r tau gm α0 col0 g) * subG r tau gm plc (pderiv ((eW r tau N).symm (α0, g)) p) := by
  rw [chain_aeval, ← (eW r tau N).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single α0]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [pderiv_lam_subG_X_eq_ite plc inj]
    simp only [Equiv.apply_symm_apply]
    first | rw [if_pos rfl] | skip
    exact mul_comm _ _
  · intro α _ hα
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [pderiv_lam_subG_X_eq_ite plc inj]
    simp only [Equiv.apply_symm_apply]
    first | rw [if_neg hα] | simp [hα]
    first | exact mul_zero _ | simp
  · intro h
    exact absurd (Finset.mem_univ _) h

end Chain

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePAllSet
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

def AllSet (V : VF C) (g : Fin 2) : Set (ℕ → I g ⊕ JJ I g → C) :=
  {L | ∃ (γ : κ → PowerSeries C) (lam : JJ I g → PowerSeries C), IsCv V γ ∧ IsCv V lam ∧
    (∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • PowerSeries.mk (fun n => L n (Sum.inl c))) ∧
    ∀ q : JJ I g, PowerSeries.mk (fun n => L n (Sum.inr q)) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun n => L n (Sum.inl c)) else 0}

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqDer
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds PartialDerivEval RowTiePCEq ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section Defs

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.dF (Y : FBChart C V O dd) (v : Fin dd → C) (j : Fin dd) : PS C 1 dd :=
  ∑ i, MvPowerSeries.C (v i) * ev (n := 1) ![pt C dd 0, 0] (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F j))

def ExDerSt (Y : FBChart C V O dd) : Prop :=
  ∀ (v : Fin dd → C) (j : Fin dd),
    ∑ i, MvPowerSeries.C (v i) * MvPowerSeries.pderiv C ((0 : Fin 1), i) (Y.ex j) = ev (n := 1) ![Y.ex] (Y.dF v j)

def GermIIMSt (Y : FBChart C V O dd) : Prop :=
  ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    IntS V ((∑ j : Fin dd, (∑ i : Fin dd, MvPowerSeries.C (v i) *
        ev (n := 2) ![pt C dd 0, 0] (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F j))) *
          MvPowerSeries.pderiv C ((0 : Fin 2), j) Y.h) + ev (n := 2) ![pt C dd 1] (Y.sgP v))

end Defs

namespace RowTiePCEqDer

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem dVar_eq {σ : Type} (w : σ) (F : MvPowerSeries σ C) : dVar w F = MvPowerSeries.pderiv C w F := by
  ext μ
  rw [MvPowerSeries.coeff_pderiv]
  show ((μ w + 1 : ℕ) : C) * MvPowerSeries.coeff (μ + Finsupp.single w 1) F = _
  push_cast
  ring

theorem pderiv_upG_same (g : Fin 2) (k : I g) (F : MvPowerSeries (I g) C) :
    MvPowerSeries.pderiv C (⟨g, k⟩ : WV I) (upG g F) = upG g (MvPowerSeries.pderiv C k F) := by
  unfold upG
  rw [Formalism.G.LogCR.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _), Finset.sum_eq_single k]
  · rw [MvPowerSeries.pderiv_X_self, mul_one]
  · intro c _ hc
    rw [MvPowerSeries.pderiv_X_of_ne, mul_zero]
    intro h
    exact hc (eq_of_heq (Sigma.mk.inj h).2)
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem pderiv_upG_ne (g g' : Fin 2) (h : g' ≠ g) (k : I g) (F : MvPowerSeries (I g') C) :
    MvPowerSeries.pderiv C (⟨g, k⟩ : WV I) (upG g' F) = 0 := by
  unfold upG
  rw [Formalism.G.LogCR.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _)]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [MvPowerSeries.pderiv_X_of_ne, mul_zero]
  intro he
  exact h (Sigma.mk.inj he).1

end RowTiePCEqDer

namespace RowTiePCEqDer

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem pderiv_uncurry (f : PS C 1 dd) (i : Fin dd) :
    MvPowerSeries.pderiv C i (un1 f) = un1 (MvPowerSeries.pderiv C ((0 : Fin 1), i) f) := by
  rw [uncurry_eq_subst, Formalism.G.LogCR.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _),
    Finset.sum_eq_single ((0 : Fin 1), i), uncurry_eq_subst]
  · rw [show (((0 : Fin 1), i) : Fin 1 × Fin dd).2 = i from rfl, MvPowerSeries.pderiv_X_self, mul_one]
  · intro q _ hq
    rw [MvPowerSeries.pderiv_X_of_ne, mul_zero]
    intro h
    exact hq (Prod.ext (Subsingleton.elim _ _) h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem uncurry_linear_combination (r : Fin dd → C) (f : Fin dd → PS C 1 dd) :
    un1 (∑ i, MvPowerSeries.C (r i) * f i) = ∑ i, MvPowerSeries.C (r i) * un1 (f i) := by
  simp only [uncurry_eq_subst]
  rw [← MvPowerSeries.coe_substAlgHom hasSubst_snd, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_C]

theorem uncurry_eval_exp_raw (Y : FBChart C V O dd) {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)
    (f : PS C 1 dd) : un1 (ev (n := 1) ![Y.ex] f) = MvPowerSeries.subst (Y.raw p).ex (un1 f) := by
  show _ = MvPowerSeries.subst (fun j => un1 (Y.ex j)) (un1 f)
  rw [eval_single_eq_subst, subst_oneVariableUncurry_eq_subst (b := fun q : Fin 1 × Fin dd => Y.ex q.2) (fun q => Y.ex_const q.2),
    subst_singlePointUncurry (fun j => by rw [constantCoeff_uncurry, Y.ex_const j])]

theorem ev_pt_dF (Y : FBChart C V O dd) (v : Fin dd → C) (g' : Fin 2) (j : Fin dd) :
    ev (n := 2) ![pt C dd g'] (Y.dF v j) =
      ∑ i, MvPowerSeries.C (v i) * ev (n := 2) ![pt C dd g', 0] (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F j)) := by
  have hZ := z0_1 (pt C (n := 2) dd g') (z0_pt g')
  have hZ' : Z0 (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) := z0_p0 _ (z0_pt 0)
  unfold FBChart.dF
  rw [ev_sum hZ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ev_mul hZ, ev_C, ev_ev hZ' hZ]
  congr 2
  funext k j'
  fin_cases k
  · exact ev_X hZ 0 j'
  · exact ev_zero hZ

theorem pderiv_lin {κ : Type} [Fintype κ] (X : RawChart C d I κ) (g : Fin 2) (k : I g) (i : κ) :
    MvPowerSeries.pderiv C k (∑ c : I g, X.u g c i • (MvPowerSeries.X c : MvPowerSeries (I g) C)) =
      MvPowerSeries.C (X.u g k i) := by
  rw [map_sum, Finset.sum_eq_single k]
  · rw [Derivation.map_smul, MvPowerSeries.pderiv_X_self, MvPowerSeries.smul_eq_C_mul, mul_one]
  · intro c _ hc
    rw [Derivation.map_smul, MvPowerSeries.pderiv_X_of_ne hc, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem pderiv_expG (Y : FBChart C V O dd) (p : PairData Y d I) (hE : ExDerSt Y) (g : Fin 2) (k : I g)
    (j : Fin dd) :
    MvPowerSeries.pderiv C k ((Y.raw p).expG g j) =
      MvPowerSeries.subst ((Y.raw p).expG g) (un1 (Y.dF ((Y.raw p).u g k) j)) := by
  have hlin0 := lin_const (Y.raw p) g
  have hL := MvPowerSeries.hasSubst_of_constantCoeff_zero hlin0
  have hx0 : ∀ i, MvPowerSeries.constantCoeff ((Y.raw p).ex i) = 0 := Y.chart_exp_constantCoeff p
  have e1 : MvPowerSeries.subst (Y.raw p).ex (un1 (Y.dF ((Y.raw p).u g k) j)) =
      ∑ i, MvPowerSeries.C ((Y.raw p).u g k i) * MvPowerSeries.pderiv C i ((Y.raw p).ex j) := by
    rw [← uncurry_eval_exp_raw Y p, ← hE, uncurry_linear_combination]
    simp only [← pderiv_uncurry]
    rfl
  unfold RawChart.expG
  rw [Formalism.G.LogCR.pderiv_subst hlin0,
    ← MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hx0) hL]
  simp only [pderiv_lin]
  rw [e1, ← MvPowerSeries.coe_substAlgHom hL, map_sum, MvPowerSeries.coe_substAlgHom]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPowerSeries.subst_mul hL, MvPowerSeries.subst_C, mul_comm]

end RowTiePCEqDer

namespace RowTiePCEqDer

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem subst_exp_eval_two {dd : ℕ} (X : RawChart C d I (Fin dd))
    (hE0 : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (X.expPt q.1 q.2) = 0) (g' : Fin 2) (f : PS C 1 dd) :
    MvPowerSeries.subst (fun q : Fin 2 × Fin dd => X.expPt q.1 q.2) (ev (n := 2) ![pt C dd g'] f) =
      MvPowerSeries.subst (X.expPt g') (un1 f) := by
  have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero hE0
  rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin 1 × Fin dd => pt C (n := 2) dd g' q.2)
      fun q => MvPowerSeries.constantCoeff_X _) hS,
    subst_singlePointUncurry (fun j => hE0 (g', j))]
  congr 1
  funext q
  rw [show (pt C (n := 2) dd g' q.2) = MvPowerSeries.X (g', q.2) from rfl, MvPowerSeries.subst_X hS]

end RowTiePCEqDer

open RowTiePCEqDer in

theorem cEqDer_of
    (hE : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
      (Y : FBChart C V O dd), ExDerSt Y)
    (hM : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
      (Y : FBChart C V O dd), GermIIMSt Y) : CEqDerSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g k
  have hvI : ∀ i, V.Ge 0 ((Y.raw p).u (1 - g) k i) := fun i => p.u_int (1 - g) k i
  have hE0 : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff ((Y.raw p).expPt q.1 q.2) = 0 := fun q => by
    rw [expPt_eq]
    exact upG_const _ (constantCoeff_subst_zero (lin_const (Y.raw p) q.1) (Y.chart_exp_constantCoeff p q.2))
  have hES := MvPowerSeries.hasSubst_of_constantCoeff_zero hE0
  have hd : ∀ (g' : Fin 2) (j : Fin dd), MvPowerSeries.pderiv C (⟨1 - g, k⟩ : WV I) ((Y.raw p).expPt g' j) =
      if g' = 1 - g then MvPowerSeries.subst ((Y.raw p).expPt (1 - g)) (un1 (Y.dF ((Y.raw p).u (1 - g) k) j))
      else 0 := by
    intro g' j
    split_ifs with hg
    · rw [hg, expPt_eq, pderiv_upG_same, pderiv_expG Y p (hE C V O dd Y) (1 - g) k j,
        upG_subst (1 - g) (a := (Y.raw p).expG (1 - g))
          (fun i => constantCoeff_subst_zero (lin_const (Y.raw p) (1 - g)) (Y.chart_exp_constantCoeff p i))]
      congr 1
      funext i
      exact (expPt_eq _ _ _).symm
    · rw [expPt_eq, pderiv_upG_ne (1 - g) g' hg k]
  have hch : MvPowerSeries.pderiv C (⟨1 - g, k⟩ : WV I)
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (Y.raw p).expPt q.1 q.2) Y.h) =
      ∑ j, MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (Y.raw p).expPt q.1 q.2)
          (MvPowerSeries.pderiv C ((1 - g : Fin 2), j) Y.h) *
        MvPowerSeries.subst ((Y.raw p).expPt (1 - g)) (un1 (Y.dF ((Y.raw p).u (1 - g) k) j)) := by
    rw [Formalism.G.LogCR.pderiv_subst hE0, Fintype.sum_prod_type, Finset.sum_eq_single (1 - g)]
    · simp only [hd, if_true]
    · intro g' _ hg'
      simp only [hd, if_neg hg', mul_zero, Finset.sum_const_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set J : PS C 2 dd := (∑ j, ev (n := 2) ![pt C dd (1 - g)] (Y.dF ((Y.raw p).u (1 - g) k) j) *
      MvPowerSeries.pderiv C ((1 - g : Fin 2), j) Y.h) + ev (n := 2) ![pt C dd g] (Y.sgP ((Y.raw p).u (1 - g) k))
    with hJd
  have hsubD : MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (Y.raw p).expPt q.1 q.2)
      (∑ j, ev (n := 2) ![pt C dd (1 - g)] (Y.dF ((Y.raw p).u (1 - g) k) j) *
        MvPowerSeries.pderiv C ((1 - g : Fin 2), j) Y.h) =
      ∑ j, MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (Y.raw p).expPt q.1 q.2)
          (MvPowerSeries.pderiv C ((1 - g : Fin 2), j) Y.h) *
        MvPowerSeries.subst ((Y.raw p).expPt (1 - g)) (un1 (Y.dF ((Y.raw p).u (1 - g) k) j)) := by
    rw [← MvPowerSeries.coe_substAlgHom hES, map_sum, MvPowerSeries.coe_substAlgHom]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPowerSeries.subst_mul hES, subst_exp_eval_two _ hE0, mul_comm]
  have hJ : IntS V J := by
    have hg2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    rcases hg2 g with rfl | rfl
    · have h := germII_holds Y _ hvI
      convert h using 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ev_pt_dF]
      rfl
    · have h := hM C V O dd Y _ hvI
      convert h using 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ev_pt_dF]
      rfl
  refine ⟨J, hJ, ?_⟩
  rw [dVar_eq]
  show MvPowerSeries.pderiv C _ (((Y.k : ℕ) : C) •
    MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (Y.raw p).expPt q.1 q.2) Y.h) = _
  rw [Derivation.map_smul, hch, ← hsubD, hJd, MvPowerSeries.subst_add hES, subst_exp_eval_two _ hE0, Y.raw_sg p,
    add_sub_cancel_right]
  rfl

end Formalism.L2.FormalSeriesBounds
end
end

