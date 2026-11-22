import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfAcyclic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2423
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2424
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogChernCocycleContractionInvariantFieldTriviali
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS.PrismDlog

noncomputable def dl {B : Type} [CommRing B] (a : DualNumber B) : B := a.snd * Ring.inverse a.fst

theorem dl_mul {B : Type} [CommRing B] {a b : DualNumber B} (ha : IsUnit a.fst) (hb : IsUnit b.fst) :
    dl (a * b) = dl a + dl b := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  have e : (a * b).fst = ((x * y : Bˣ) : B) := by simp [hx, hy]
  have e2 : (a * b).snd = a.fst * b.snd + a.snd * b.fst := by
    rw [TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  have h1 : (x : B) * ((x⁻¹ : Bˣ) : B) = 1 := Units.mul_inv x
  have h2 : (y : B) * ((y⁻¹ : Bˣ) : B) = 1 := Units.mul_inv y
  rw [dl, dl, dl, e, e2, Ring.inverse_unit, ← hx, ← hy, Ring.inverse_unit, Ring.inverse_unit, mul_inv_rev,
    Units.val_mul]
  linear_combination (b.snd * ((y⁻¹ : Bˣ) : B)) * h1 + (a.snd * ((x⁻¹ : Bˣ) : B)) * h2

theorem dl_inl {B : Type} [CommRing B] (b : B) : dl (TrivSqZeroExt.inl b : DualNumber B) = 0 := by
  simp [dl]

theorem dl_one_add {B : Type} [CommRing B] {a : DualNumber B} (ha : a.fst = 0) : dl (1 + a) = a.snd := by
  simp [dl, ha]

theorem dl_map {R B B' : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (ρ : B →ₐ[R] B')
    {a : DualNumber B} (ha : IsUnit a.fst) : dl (dualAlg ρ a) = ρ (dl a) := by
  obtain ⟨x, hx⟩ := ha
  have e : (dualAlg ρ a).fst = ((Units.map (ρ : B →* B') x : B'ˣ) : B') := by simp [hx]
  rw [dl, dl, e, ← hx, Ring.inverse_unit, Ring.inverse_unit, snd_dualAlg, map_mul]
  simp

theorem snd_eq_of_mul {B : Type} [CommRing B] {l U X Y : DualNumber B} (hl : l.fst = 0) (hU : IsUnit U.fst)
    (hX : IsUnit X.fst) (hY : IsUnit Y.fst) (h : (1 + l) * U = X * Y) : l.snd = dl X + dl Y - dl U := by
  have h1 : IsUnit (1 + l).fst := by simp [hl]
  have := congrArg dl h
  rw [dl_mul h1 hU, dl_mul hX hY, dl_one_add hl] at this
  rw [← this]; ring

theorem isUnit_fst {B : Type} [CommRing B] {a : DualNumber B} (h : IsUnit a) : IsUnit a.fst :=
  h.map (TrivSqZeroExt.fstHom B B B)

theorem valR_cocycle {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {C : Type} [CommRing C] (w : Sp C ⟶ X)
    (a b k : L.ι) (h : ⊤ ≤ w ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U k)) :
    valR w _ (L.g a b).val * valR w _ (L.g b k).val = valR w _ (L.g a k).val := by
  have := congrArg (fun z ↦ valR w _ (z : Γ(X, L.U a ⊓ L.U b ⊓ L.U k)ˣ).val) (hL.cocycle a b k)
  simp only [Units.val_mul] at this
  rw [GlobalTheory.Points.valR_mul w _ h] at this
  simp only [res, Units.coe_map, MonoidHom.coe_coe] at this
  rwa [GlobalTheory.Points.valR_res w _ h, GlobalTheory.Points.valR_res w _ h, GlobalTheory.Points.valR_res w _ h] at this

theorem isUnit_valR {X : Scheme.{0}} {C : Type} [CommRing C] (w : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (f : Γ(X, U)ˣ) : IsUnit (valR w U f.val) := by
  rw [GlobalTheory.Points.valR_eq w U h]; exact f.isUnit.map _

theorem evalAt_eq_valR {X : Scheme.{0}} {C : Type} [CommRing C] (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : evalAt x U h f = valR x U f := by
  rw [valR, dif_pos h]; rfl

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

theorem fst_valR_trx (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) (U : A.left.Opens) (h : P.In U)
    (f : Γ(A.left, U)) : (valR (P.trx v) U f).fst = valR P.x U f := by
  have e := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom P.B P.B P.B).toRingHom (P.trx v) U (h.tr hv) f
  rw [(P.isTransl_trx v).red hv] at e
  rw [e]; rfl

theorem snd_l (L : LB A.left) (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T))
    (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U))
    (hu : ∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T))
      (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val)
    (hl : ∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ)
    (R : GPt A) (hR : ∃ i, R.In (L.U i)) {T T' : Small L.U} (φ : T ⟶ T') (ψ : T' ⟶ ⟨R.ext, hR⟩) :
    TrivSqZeroExt.snd (R := R.B) (l T T' ⟨R.ext, hR⟩ φ ψ : DualNumber R.B) =
      dl (ψ.hom.φ (u T T' φ) : DualNumber R.B) + dl (u T' ⟨R.ext, hR⟩ ψ : DualNumber R.B) -
        dl (u T ⟨R.ext, hR⟩ (φ ≫ ψ) : DualNumber R.B) := by
  have hunit : ∀ (T T' : Small L.U) (φ : T ⟶ T'), IsUnit (T'.obj.π (u T T' φ)) := fun T T' φ ↦ by
    rw [hu]; exact (L.g _ _).isUnit.map _
  obtain ⟨hmem, heq⟩ := hl T T' ⟨R.ext, hR⟩ φ ψ
  rw [dpExp_sqDP _ hmem] at heq
  refine snd_eq_of_mul hmem (hunit T ⟨R.ext, hR⟩ (φ ≫ ψ)) ?_ (hunit T' ⟨R.ext, hR⟩ ψ) heq
  have e := ψ.hom.comm (u T T' φ)
  change _ = TrivSqZeroExt.fst _ at e
  rw [← e]
  exact (hunit T T' φ).map _

theorem snd_l' (L : LB A.left) (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T))
    (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U))
    (hu : ∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T))
      (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val)
    (hl : ∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ)
    (R : GPt A) (hR : ∃ i, R.In (L.U i)) {T T' : Small L.U} (φ : T ⟶ T') (ψ : T' ⟶ ⟨R.ext, hR⟩)
    (χ : T ⟶ ⟨R.ext, hR⟩) (hχ : φ ≫ ψ = χ) :
    TrivSqZeroExt.snd (R := R.B) (l T T' ⟨R.ext, hR⟩ φ ψ : DualNumber R.B) =
      dl (ψ.hom.φ (u T T' φ) : DualNumber R.B) + dl (u T' ⟨R.ext, hR⟩ ψ : DualNumber R.B) -
        dl (u T ⟨R.ext, hR⟩ χ : DualNumber R.B) := by
  subst hχ; exact snd_l L c hc u l hu hl R hR φ ψ

open Classical in

noncomputable def Nf (L : LB A.left) (c : Small L.U → L.ι) (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B)
    {v : epsR K ⟶ A} (hv : IsTangent v) (j : L.ι) : PtFn (A.hom ≫ 𝟙 (Sp K)) := fun P ↦
  if h : P.In (L.U j) then
    dl (u ⟨P.triv, ⟨j, h⟩⟩ ⟨P.ext, ⟨j, h⟩⟩ ⟨P.sec⟩ : DualNumber P.B) -
      dl (u ⟨(P.tr v).triv, ⟨j, h.tr hv⟩⟩ ⟨P.ext, ⟨j, h⟩⟩ ⟨P.tan hv⟩ : DualNumber P.B) -
      dl (valR (P.trx v) _ (L.g (c ⟨(P.tr v).triv, ⟨j, h.tr hv⟩⟩) j).val)
  else 0

end GlobalTheory.CechKS.PrismDlog

open GlobalTheory.CechKS.PrismDlog in

theorem GlobalTheory.CechKS.prism_trivialised : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T)) (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U)), (∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T)) (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val) → (∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧ dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ) → ∀ (v : epsR K ⟶ A) (hv : IsTangent v), ∃ N : L.ι → PtFn (A.hom ≫ 𝟙 (Sp K)), (∀ (j : L.ι) (P Q : GPt A) (φ : P.Hom Q) (hP : P.In (L.U j)), prism l hv φ ⟨j, hP⟩ = N j Q - φ.ρ (N j P)) ∧ ∀ (j j' : L.ι) (P : GPt A), P.In (L.U j) → P.In (L.U j') → N j P - N j' P = dlog L v j j' P := by
  intro K _ A _ L hL c hc u l hu hl v hv
  have hunit : ∀ (T T' : Small L.U) (φ : T ⟶ T'), IsUnit (T'.obj.π (u T T' φ)) := fun T T' φ ↦ by
    rw [hu]; exact (L.g _ _).isUnit.map _
  refine ⟨Nf L c u hv, ?_, ?_⟩
  · intro j P Q φ hP
    have hQ : Q.In (L.U j) := hP.map φ
    have k1 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨P.triv, ⟨j, hP⟩⟩) (T' := ⟨Q.triv, ⟨j, hQ⟩⟩) ⟨φ.triv⟩ ⟨Q.sec⟩
      ⟨P.sec ≫ φ.dual⟩ (by
        ext b
        · show (TrivSqZeroExt.inl (φ.ρ b) : DualNumber Q.B).fst = (dualAlg φ.ρ (TrivSqZeroExt.inl b)).fst
          simp
        · show (TrivSqZeroExt.inl (φ.ρ b) : DualNumber Q.B).snd = (dualAlg φ.ρ (TrivSqZeroExt.inl b)).snd
          simp)
    have k2 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨P.triv, ⟨j, hP⟩⟩) (T' := ⟨P.ext, ⟨j, hP⟩⟩) ⟨P.sec⟩ ⟨φ.dual⟩
      ⟨P.sec ≫ φ.dual⟩ rfl
    have k3 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩)
      (T' := ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩) ⟨(φ.tr v).triv⟩ ⟨Q.tan hv⟩ ⟨P.tan hv ≫ φ.dual⟩ (by ext b <;> rfl)
    have k4 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩)
      (T' := ⟨P.ext, ⟨j, hP⟩⟩) ⟨P.tan hv⟩ ⟨φ.dual⟩ ⟨P.tan hv ≫ φ.dual⟩ rfl
    obtain ⟨a, ha⟩ : ∃ a, a = c ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = c ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ := ⟨_, rfl⟩
    have hPa : (P.tr v).In (L.U a) := ha ▸ hc ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩
    have hQb : (Q.tr v).In (L.U b) := hb ▸ hc ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩
    have hQa : (Q.tr v).In (L.U a) := hPa.map (φ.tr v)
    have e1 : (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ ⟨(φ.tr v).triv⟩ : DualNumber Q.B) =
        valR (Q.trx v) _ (L.g b a).val := by
      subst ha hb
      exact (hu ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ ⟨(φ.tr v).triv⟩).trans
        (evalAt_eq_valR _ _ _ _)
    have e2 : valR (Q.trx v) _ (L.g a j).val = dualAlg φ.ρ (valR (P.trx v) _ (L.g a j).val) := by
      have e := GlobalTheory.Points.valR_spMap_comp (dualAlg φ.ρ : DualNumber P.B →+* DualNumber Q.B) (P.trx v) _
        (hPa.inf (hP.tr hv)) (L.g a j).val
      have e' : spMap (dualAlg φ.ρ : DualNumber P.B →+* DualNumber Q.B) ≫ P.trx v = Q.trx v := (φ.tr v).pt
      rw [e'] at e
      exact e
    have e3 := valR_cocycle L hL (Q.trx v) b a j ((hQb.inf hQa).inf (hQ.tr hv))
    have e4 : dl (valR (Q.trx v) _ (L.g b j).val) =
        dl (valR (Q.trx v) _ (L.g b a).val) + φ.ρ (dl (valR (P.trx v) _ (L.g a j).val)) := by
      rw [← e3, dl_mul (isUnit_fst (isUnit_valR _ _ (hQb.inf hQa) _))
        (isUnit_fst (isUnit_valR _ _ (hQa.inf (hQ.tr hv)) _)), e2,
        dl_map _ (isUnit_fst (isUnit_valR _ _ (hPa.inf (hP.tr hv)) _))]
    have d1 : dl (Q.sec.φ (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨Q.triv, ⟨j, hQ⟩⟩ ⟨φ.triv⟩) : DualNumber Q.B) = 0 := dl_inl _
    have d2 : dl (φ.dual.φ (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩) : DualNumber Q.B) =
        φ.ρ (dl (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩ : DualNumber P.B)) :=
      dl_map φ.ρ (hunit ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩)
    have d3 : dl ((Q.tan hv).φ (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩
        ⟨(φ.tr v).triv⟩) : DualNumber Q.B) = dl (valR (Q.trx v) _ (L.g b a).val) := congrArg dl e1
    have d4 : dl (φ.dual.φ (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩) : DualNumber Q.B) =
        φ.ρ (dl (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩ : DualNumber P.B)) :=
      dl_map φ.ρ (hunit ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩)
    have k1' := k1.trans (congrArg (fun z ↦ z + _ - _) d1)
    have k2' := k2.trans (congrArg (fun z ↦ z + _ - _) d2)
    have k3' := k3.trans (congrArg (fun z ↦ z + _ - _) d3)
    have k4' := k4.trans (congrArg (fun z ↦ z + _ - _) d4)
    have key : ∀ {x1 x2 x3 x4 : DualNumber Q.B} {y1 y2 y3 y4 : Q.B}, x1.snd = y1 → x2.snd = y2 → x3.snd = y3 →
        x4.snd = y4 → ((x1 - x2) - (x3 - x4)).snd = (y1 - y2) - (y3 - y4) := by
      rintro x1 x2 x3 x4 _ _ _ _ rfl rfl rfl rfl
      simp
    refine (key k1' k2' k3' k4').trans ?_
    simp only [Nf, dif_pos hP, dif_pos hQ, map_sub]
    rw [← ha, ← hb, e4]
    ring
  · intro j j' P hj hj'
    obtain ⟨b, hb⟩ : ∃ b, b = c ⟨(P.tr v).triv, ⟨j, hj.tr hv⟩⟩ := ⟨_, rfl⟩
    have hPb : (P.tr v).In (L.U b) := hb ▸ hc ⟨(P.tr v).triv, ⟨j, hj.tr hv⟩⟩
    simp only [Nf, dif_pos hj, dif_pos hj']
    rw [← hb]
    have e3 := valR_cocycle L hL (P.trx v) b j j' ((hPb.inf (hj.tr hv)).inf (hj'.tr hv))
    have e4 : dl (valR (P.trx v) _ (L.g b j').val) =
        dl (valR (P.trx v) _ (L.g b j).val) + dl (valR (P.trx v) _ (L.g j j').val) := by
      rw [← e3, dl_mul (isUnit_fst (isUnit_valR _ _ (hPb.inf (hj.tr hv)) _))
        (isUnit_fst (isUnit_valR _ _ ((hj.inf hj').tr hv) _))]
    have e5 : dl (valR (P.trx v) _ (L.g j j').val) = dlog L v j j' P := by
      rw [dl, dlog, fst_valR_trx P hv _ (hj.inf hj')]
      have h1 : valR P.x _ (L.g j j').val * valR P.x _ (L.g j j')⁻¹.val = 1 := by
        rw [← GlobalTheory.Points.valR_mul _ _ (hj.inf hj'), Units.mul_inv, GlobalTheory.Points.valR_eq _ _ (hj.inf hj'), map_one]
      have h2 : Ring.inverse (valR P.x _ (L.g j j').val) = valR P.x _ (L.g j j')⁻¹.val :=
        Ring.inverse_unit (Units.mkOfMulEqOne _ _ h1)
      rw [h2]
    rw [← e5, e4]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisSectionsSplit
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open Opposite

namespace GlobalTheory.TwoOpens

theorem sections_inter_eq_sub_of_subsingleton_cohOn : ∀ (Y : Scheme.{0}) (F : Y.Modules) (W₁ W₂ : Y.Opens), Subsingleton (cohOn F (W₁ ⊔ W₂) 1) → ∀ t : sectionsOn F (W₁ ⊓ W₂), ∃ (a : sectionsOn F W₁) (b : sectionsOn F W₂), t = sectionsOn.res Γ(Y, ⊤) F inf_le_right b - sectionsOn.res Γ(Y, ⊤) F inf_le_left a := by
  intro Y F W₁ W₂ h t
  let A := (toAbSheaf Y).obj F
  let S := Flasque.injectiveShortComplex A
  have hS : S.ShortExact := Flasque.injectiveShortComplex_shortExact A
  have hfl : TopCat.Sheaf.IsFlasque S.X₂ := Flasque.isFlasque_injectiveShortComplex_X₂ A
  have hinj : ∀ W : Y.Opens, Function.Injective (S.f.hom.app (op W)) := by
    intro W x y hxy
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective x
    obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
    rw [← SheafLES.equivZero_map, ← SheafLES.equivZero_map] at hxy
    rw [SheafLES.injective_zero hS W ((SheafLES.equivZero.{0} S.X₂ W).injective hxy)]
  have hex : ∀ W : Y.Opens, Function.Exact (S.f.hom.app (op W)) (S.g.hom.app (op W)) := by
    intro W x
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₂ W).surjective x
    rw [← SheafLES.equivZero_map, AddEquiv.map_eq_zero_iff, SheafLES.exact₂ hS 0 W x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (SheafLES.equivZero_map S.f W y).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
      exact ⟨y, (SheafLES.equivZero.{0} S.X₂ W).injective
        ((SheafLES.equivZero_map S.f W y).trans hy)⟩

  have natf : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.f.hom.app (op V) (S.X₁.obj.map (homOfLE hUV).op x) =
        S.X₂.obj.map (homOfLE hUV).op (S.f.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.f.hom (homOfLE hUV).op x
  have natg : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.g.hom.app (op V) (S.X₂.obj.map (homOfLE hUV).op x) =
        S.X₃.obj.map (homOfLE hUV).op (S.g.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.g.hom (homOfLE hUV).op x
  have resres : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₂.obj.map (homOfLE h₂).op (S.X₂.obj.map (homOfLE h₁).op x) =
        S.X₂.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have resres3 : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₃.obj.map (homOfLE h₂).op (S.X₃.obj.map (homOfLE h₁).op x) =
        S.X₃.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

  obtain ⟨b', hb'⟩ := (AddCommGrpCat.epi_iff_surjective
    (S.X₂.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op)).1 (hfl.epi _)
    (S.f.hom.app (op (W₁ ⊓ W₂)) (sectionsOn.toΓ F _ t))

  let U : Bool → Y.Opens := fun b => cond b W₂ W₁
  let sf : ∀ b : Bool, ToType (S.X₃.obj.obj (op (U b))) := fun b =>
    match b with
    | true => S.g.hom.app (op W₂) b'
    | false => 0
  have h0 : S.X₃.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    rw [← natg, hb']
    exact (hex _).apply_apply_eq_zero _
  have h0' : S.X₃.obj.map (homOfLE (inf_le_left : W₂ ⊓ W₁ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    have e := resres3 (inf_le_right : W₁ ⊓ W₂ ≤ W₂) (inf_comm W₂ W₁).le (S.g.hom.app (op W₂) b')
    rw [h0, map_zero] at e
    exact e.symm
  have hcomp : TopCat.Presheaf.IsCompatible S.X₃.obj U sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact (map_zero _).trans h0.symm
    · exact h0'.trans (map_zero _).symm
    · rfl
  obtain ⟨q, hq, -⟩ := TopCat.Sheaf.existsUnique_gluing' (X := Y.toPresheafedSpace.carrier) S.X₃ U (W₁ ⊔ W₂)
    (fun b => homOfLE (by cases b; exacts [le_sup_left, le_sup_right]))
    (sup_le (le_iSup U false) (le_iSup U true)) sf hcomp

  obtain ⟨i, hi⟩ := SheafLES.sections_surjective_of_subsingleton.{0} hS (W₁ ⊔ W₂) h q
  obtain ⟨bb, hbb⟩ := (hex W₂ (b' - S.X₂.obj.map (homOfLE (le_sup_right : W₂ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_sub, natg, hi]
    exact sub_eq_zero.2 (hq true).symm)
  obtain ⟨aa, haa⟩ := (hex W₁ (- S.X₂.obj.map (homOfLE (le_sup_left : W₁ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_neg, natg, hi]
    exact neg_eq_zero.2 (hq false))
  refine ⟨(sectionsOn.toΓ F W₁).symm aa, (sectionsOn.toΓ F W₂).symm bb, ?_⟩
  apply (sectionsOn.toΓ F _).injective
  rw [map_sub, sectionsOn.toΓ_res, sectionsOn.toΓ_res]
  simp only [AddEquiv.apply_symm_apply]
  apply hinj
  change _ = S.f.hom.app _ (S.X₁.obj.map _ bb - S.X₁.obj.map _ aa)
  erw [map_sub]
  rw [natf, natf, hbb, haa, map_sub, map_neg, resres, resres, hb']
  abel

end GlobalTheory.TwoOpens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCartierMultipleChartIffRegularCodimOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cartierMultiple_chart_iff_regular_codimOne : ∀ (σ : Setup) (x : Sp σ.R) (k : ℕ) (v : (σ.C x).G.left.functionField), v ∈ Sec (σ.D₁ x) k ↔ (∀ z : (σ.V x).toScheme, (k • σ.D₁ x).RegularAt ((σ.V x).ι z) v) ∧ ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → RegAt z v := by
  first | exact @GlobalTheory.Desc.ChartHartogs.mem_sec_iff | exact GlobalTheory.Desc.ChartHartogs.mem_sec_iff | (intros; apply GlobalTheory.Desc.ChartHartogs.mem_sec_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O
open scoped NNReal

namespace GlobalTheory.VertForm

section Algebra

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {D : ℕ}

variable (E D) in

abbrev Form : Type u := MultilinearMap ℝ (fun _ : Fin (D + 1) => E) ℝ

def IsSymm (num : Form E D) : Prop := ∀ (v : Fin (D + 1) → E) (π : Equiv.Perm (Fin (D + 1))), num (v ∘ π) = num v

def rad (num : Form E D) : Submodule ℝ E where
  carrier := {x | ∀ (v : Fin (D + 1) → E) (j : Fin (D + 1)), num (Function.update v j x) = 0}
  add_mem' hx hy v j := by rw [num.map_update_add, hx v j, hy v j, add_zero]
  zero_mem' v j := num.map_update_zero v j
  smul_mem' c x hx v j := by rw [num.map_update_smul, hx v j, smul_zero]

theorem map_congr_rad (num : Form E D) {v w : Fin (D + 1) → E} (h : ∀ j, v j - w j ∈ rad num) : num v = num w := by
  classical
  have key (S : Finset (Fin (D + 1))) : num (S.piecewise v w) = num w := by
    induction S using Finset.induction_on with
    | empty => rw [Finset.piecewise_empty]
    | insert j S hj ih =>
      have e : v j = (v j - w j) + w j := by abel
      rw [Finset.piecewise_insert, e, num.map_update_add, h j, zero_add, ← Finset.piecewise_eq_of_notMem S v w hj,
        Function.update_eq_self, ih]
  rw [← key Finset.univ, Finset.piecewise_univ]

def cone (num : Form E D) (G : Set E) : Set E := {x | ∃ z ∈ Submodule.span ℝ≥0 G, x - z ∈ rad num}

variable {num : Form E D} {G : Set E}

theorem mem_cone_of_mem {x : E} (h : x ∈ G) : x ∈ cone num G := ⟨x, Submodule.subset_span h, by simp⟩

theorem zero_mem_cone : (0 : E) ∈ cone num G := ⟨0, zero_mem _, by simp⟩

theorem add_mem_cone {x y : E} (hx : x ∈ cone num G) (hy : y ∈ cone num G) : x + y ∈ cone num G := by
  obtain ⟨z, hz, h⟩ := hx
  obtain ⟨w, hw, h'⟩ := hy
  exact ⟨z + w, add_mem hz hw, by rw [add_sub_add_comm]; exact add_mem h h'⟩

theorem smul_mem_cone {x : E} {c : ℝ} (hc : 0 ≤ c) (hx : x ∈ cone num G) : c • x ∈ cone num G := by
  obtain ⟨z, hz, h⟩ := hx
  exact ⟨c • z, Submodule.smul_mem _ (⟨c, hc⟩ : ℝ≥0) hz, by rw [← smul_sub]; exact Submodule.smul_mem _ c h⟩

theorem sum_mem_cone {ι : Type*} (s : Finset ι) {x : ι → E} (h : ∀ i ∈ s, x i ∈ cone num G) :
    ∑ i ∈ s, x i ∈ cone num G :=
  Finset.sum_induction x (· ∈ cone num G) (fun _ _ => add_mem_cone) zero_mem_cone h

theorem mem_cone_of_rad {x y : E} (hy : y ∈ cone num G) (h : x - y ∈ rad num) : x ∈ cone num G := by
  obtain ⟨z, hz, h'⟩ := hy
  exact ⟨z, hz, by rw [← sub_add_sub_cancel x y z]; exact add_mem h h'⟩

end Algebra

section Bundles

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {p : X ⟶ Sp k} {q : X' ⟶ Sp k}

variable (p) in

abbrev Cl : Type 1 := HermLB p →₀ ℝ

def cl (L : HermLB p) : Cl p := Finsupp.single L 1

def pullCl (π : X' ⟶ X) (hπ : π ≫ p = q) : Cl p →ₗ[ℝ] Cl q := Finsupp.lmapDomain ℝ ℝ fun L => L.pull π hπ

theorem pullCl_cl (π : X' ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) : pullCl π hπ (cl L) = cl (L.pull π hπ) :=
  Finsupp.mapDomain_single

def IsArForm [IsIntegral X] (D : ℕ) (num : Form (Cl p) D) : Prop :=
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), IsArFun L D Φ →
    ∀ a : Fin (D + 1) → ι → ℝ, Φ (∏ j, lin (a j)) = num fun j => ∑ i, a j i • cl (L i)

variable (p) in

def oneB : HermLB p := fnB (fun _ _ => 2) (fun _ y => CxPts.cInfAt_const 2 y) fun _ _ _ _ _ _ _ => rfl

def NefOver (L : HermLB p) (l : ℕ) : Prop :=
  ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
    [Field κ] [Finite κ] [CharP κ l] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection κ (L.B.pull i) 1

theorem nefFib_iff (L : HermLB p) : NefFib L ↔ ∀ l : ℕ, l.Prime → NefOver L l :=
  ⟨fun h _ _ Z i _ _ κ _ _ _ _ hZ => h Z i κ hZ, fun h Z i _ _ κ _ _ _ hZ =>
    h (ringChar κ) (CharP.char_is_prime κ _) Z i κ hZ⟩

end Bundles

section Covers

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Lies (V' V : Cover Y) (π : V'.X ⟶ V.X) : Prop := ∃ g : V'.G ⟶ V.G, g ≫ V.j = V'.j ≫ π ∧ g ≫ V.π = V'.π

theorem lies_id (V : Cover Y) : Lies V V (𝟙 _) := ⟨𝟙 _, by simp, by simp⟩

end Covers

end GlobalTheory.VertForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelDiagonalRestrictionOfSymmetricTrivialStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_kernel_diagonal_restriction_of_symmetric_trivial : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) a := by
  first | exact @GlobalTheory.AbDual.memKL_diag_of_triv_ev_of_symm | exact GlobalTheory.AbDual.memKL_diag_of_triv_ev_of_symm | (intros; apply GlobalTheory.AbDual.memKL_diag_of_triv_ev_of_symm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelLiftOneOfAxisTrivialBundleStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_kernel_lift_one_of_axis_trivial_bundle : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL (G ⊗ G) P (lift a (1 : T ⟶ G)) := by
  first | exact @GlobalTheory.AbDual.memKL_lift_one_of_triv_ev | exact GlobalTheory.AbDual.memKL_lift_one_of_triv_ev | (intros; apply GlobalTheory.AbDual.memKL_lift_one_of_triv_ev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfLineBundleOfDualPairLeftTrivialStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_kernelOfLineBundle_of_dualPair_left_trivial : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (L : LB A.left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → L.IsLB → ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → GlobalTheory.MemKL A L x := by
  first | exact @GlobalTheory.AbDual.memKL_of_triv_ev_left | exact GlobalTheory.AbDual.memKL_of_triv_ev_left | (intros; apply GlobalTheory.AbDual.memKL_of_triv_ev_left <;> assumption)
end

