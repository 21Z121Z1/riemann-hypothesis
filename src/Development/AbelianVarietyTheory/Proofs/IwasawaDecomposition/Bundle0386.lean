import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0380
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdHstar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0382
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterFiniteIdeleValueMemField
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.HeckeValField

variable {E : Type} [Field E] [NumberField E]

def unitsIn (M : IntermediateField ℚ ℂ) : Subgroup ℂˣ where
  carrier := {z | (z : ℂ) ∈ M}
  one_mem' := by simpa using M.one_mem
  mul_mem' := fun {a b} ha hb => by simpa using M.mul_mem ha hb
  inv_mem' := fun {a} ha => by simpa using M.inv_mem ha

theorem mem_unitsIn {M : IntermediateField ℚ ℂ} {z : ℂˣ} : z ∈ unitsIn M ↔ (z : ℂ) ∈ M := Iff.rfl

theorem val_mem (χ : HChar E) {M : IntermediateField ℚ ℂ} (hM : valueField χ 0 ≤ M)
    {v : HeightOneSpectrum (𝓞 E)} (hv : χ.UnrAt v) : χ.val v ∈ unitsIn M := by
  have h := hM (IntermediateField.subset_adjoin ℚ (valueSet χ 0) ⟨v, hv, rfl⟩)
  exact mem_unitsIn.2 (by simpa [HChar.valTw] using h)

theorem loc_mem_of_unrAt (χ : HChar E) {G : Subgroup ℂˣ} {v : HeightOneSpectrum (𝓞 E)} (hv : χ.UnrAt v)
    (hval : χ.val v ∈ G) (y : (v.adicCompletion E)ˣ) : χ.loc v y ∈ G := by
  set π := atFin v (unif v)
  have hπ : Valued.v (π : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := unif_spec v
  have hy0 : Valued.v (y : v.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  set k := WithZero.log (Valued.v (y : v.adicCompletion E))
  have hy : Valued.v (y : v.adicCompletion E) = WithZero.exp k := (WithZero.exp_log hy0).symm
  have hu : IsUnitAt v (y * π ^ k) := by
    unfold IsUnitAt
    rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, hy, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h1 := hv _ hu
  rw [map_mul, map_zpow] at h1
  rw [eq_inv_of_mul_eq_one_left h1]
  exact G.inv_mem (G.zpow_mem hval k)

theorem loc_mem (χ : HChar E) {M : IntermediateField ℚ ℂ} (hM : valueField χ 0 ≤ M)
    (hinf : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) (v : HeightOneSpectrum (𝓞 E)) (y : (v.adicCompletion E)ˣ) :
    χ.loc v y ∈ unitsIn M := by
  classical
  set G := unitsIn M
  by_cases hv : χ.UnrAt v
  · exact loc_mem_of_unrAt χ hv (val_mem χ hM hv) y
  set R := (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
  have hR : ∀ w, w ∉ R → χ.UnrAt w := fun w hw => by
    by_contra h
    exact hw ((GlobalTheory.Mem.UnrAe.finite_ramified χ).mem_toFinset.2 h)
  choose nf hnf using GlobalTheory.HeckeSplit.exists_level χ.1 χ.2.1
  set S := insert v R
  set N := S.sup nf
  obtain ⟨a, ha0, hav, haw⟩ := GlobalTheory.HkFin.exists_weak_approx_unit E R v y N
  set k : Eˣ := Units.mk0 a ha0
  have h1 : χ.loc v y = χ.locK v k := by
    have hle : nf v ≤ N := Finset.le_sup (Finset.mem_insert_self v R)
    have e : χ.loc v (atFin v k * y⁻¹) = 1 := by
      apply hnf v
      refine le_trans ?_ (WithZero.exp_le_exp.mpr (by omega : -(N : ℤ) ≤ -(nf v : ℤ)))
      exact hav
    rw [map_mul, map_inv, mul_inv_eq_one] at e
    exact e.symm
  have h2 : ∀ w ∈ S, w ≠ v → χ.locK w k = 1 := by
    intro w hw hwv
    have hwR : w ∈ R := (Finset.mem_insert.1 hw).resolve_left hwv
    have hle : nf w ≤ N := Finset.le_sup hw
    apply hnf w
    have e : ((atFin w k : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        algebraMap E (w.adicCompletion E) (a - 1) := by
      rw [map_sub, map_one]; rfl
    rw [e, PI.FinOrdValD.WA.val_alg]
    exact (haw w hwR hwv).trans (WithZero.exp_le_exp.mpr (by omega))
  have hpr := χ.productRule S (fun w hw => hR w fun h => hw (Finset.mem_insert_of_mem h)) k
  rw [Finset.prod_eq_single_of_mem v (Finset.mem_insert_self v R) (fun w hw hwv => h2 w hw hwv)] at hpr
  have hF : (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : w ∉ S), χ.val w ^ ordF w k) ∈ G := by
    refine finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun w => ?_
    refine finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun hw => ?_
    exact G.zpow_mem (val_mem χ hM (hR w fun h => hw (Finset.mem_insert_of_mem h))) _
  have h3 : χ.locK v k * (χ.inf k * ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : w ∉ S), χ.val w ^ ordF w k) = 1 := by
    rw [← hpr]; ac_rfl
  rw [h1, eq_inv_of_mul_eq_one_left h3]
  exact G.inv_mem (G.mul_mem (hinf k) hF)

theorem mem_of_inf_eq_one : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (M : IntermediateField ℚ ℂ),
    valueField χ 0 ≤ M → (∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ x, (∀ w : InfinitePlace E,
      (x.val : AdeleRing (𝓞 E) E).1 w = 1) → ((χ.1 x : ℂˣ) : ℂ) ∈ M := by
  intro E _ _ χ M hM hinf x hx
  classical
  have hev : ∀ᶠ v in Filter.cofinite, Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) :
      v.adicCompletion E) = 1 := by
    have h1 : ∀ᶠ v in Filter.cofinite, (x.val.2 : FiniteAdeleRing (𝓞 E) E).1 v ∈ v.adicCompletionIntegers E :=
      x.val.2.2
    have h2 : ∀ᶠ v in Filter.cofinite, (x⁻¹.val.2 : FiniteAdeleRing (𝓞 E) E).1 v ∈ v.adicCompletionIntegers E :=
      x⁻¹.val.2.2
    filter_upwards [h1, h2] with v hv1 hv2
    have e1 : Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv1
    have e2 : Valued.v ((GlobalTheory.HeckeSplit.finPart E v x⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv2
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀] at e2
    have h0 : 0 < Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).mpr (Units.ne_zero _))
    exact le_antisymm e1 ((inv_le_one₀ h0).1 e2)
  have hfin := Filter.eventually_cofinite.1 hev
  set S := hfin.toFinset ∪ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
  have hS : ∀ v ∉ S, χ.1 (HeckeValGen.localIdele E v (GlobalTheory.HeckeSplit.finPart E v x)) = 1 := by
    intro v hv
    have hu : ¬ ¬ Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1 :=
      fun h => hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 h))
    have hr : χ.UnrAt v := by
      by_contra h
      exact hv (Finset.mem_union_right _ ((GlobalTheory.Mem.UnrAe.finite_ramified χ).mem_toFinset.2 h))
    exact hr _ (not_not.1 hu)
  rw [GlobalTheory.HeckeSplit.char_eq_prod_local χ.1 χ.2.1 x S hS]
  have hinfx : GlobalTheory.HeckeSplit.infPart E x = 1 := Units.ext (funext fun w => hx w)
  rw [hinfx, map_one, map_one, one_mul]
  exact mem_unitsIn.1 ((unitsIn M).prod_mem fun v _ => loc_mem χ hM hinf v _)

end GlobalTheory.HeckeValField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeIdempotentProjectorVanishingBaseChangeTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem transfer_aeval (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (F : Module.End D.what₂.LL (S.WL j)) (G : Module.End (FractionRing (T.O i)) (FmT D T S i j b))
    (hFG : ∀ x, Φ (F x) = G (Φ x)) (p : Polynomial ↥D.LL0) (x : S.WL j) :
    Φ (aeval F (p.map (algebraMap ↥D.LL0 D.what₂.LL)) x) = aeval G (p.map (readT D T i b)) (Φ x) := by
  have hpow : ∀ (n : ℕ) (y : S.WL j), Φ ((F ^ n) y) = (G ^ n) (Φ y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hFG]
  induction p using Polynomial.induction_on' generalizing x with
  | add p q hp hq => rw [Polynomial.map_add, Polynomial.map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      map_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, IntermediateField.algebraMap_apply,
      hc, hpow]

theorem transfer_piLop (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (x : S.WL j) : Φ (piLop D S In.θ j x) = piKop D T S In i j b (Φ x) := by
  haveI : Fintype (Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _
  unfold piLop piKop
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hc, ha, LinearEquiv.coe_coe]

theorem phiKop_eGT_piKop_eq_zero : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ)
    (b : Bool) (k : ℕ) (P : PlE D.host),
    1 ≤ j → j ≤ D.R.m → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 →
    phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b = 0 := by
  intro D T S In i j b k P h1 h2 h0
  obtain ⟨Φ, hc, hf, hw⟩ := descend_exists D T S In i j b h1 h2
  have ha := descend_actL D T S In i j b h1 h2 Φ hc hf
  have he : ∀ x, Φ (eLop D S j x) = eGT D T S In.rho In.chi i j b (Φ x) := descend_eSum D T S In i j b Φ hc ha
  have hpi := transfer_piLop D T S In i j b Φ hc ha
  have hr : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    split_ifs with h
    · rfl
    · exact absurd ⟨h1, h2⟩ h
  have hh : ∀ x, Φ (In.hL j k P x) = hLT D T S In i j b k P (Φ x) := fun x => hf _ _ hr x
  have hphi : ∀ x, Φ (phiLop D S In j k P x) = phiKop D T S In i j b k P (Φ x) :=
    transfer_aeval D T S i j b Φ hc _ _ hh (evPol D S In j k P)
  have key : ∀ w : ↥(WKr D S j),
      (phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b)
        ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = 0 := by
    intro w
    rw [← hw, Module.End.mul_apply, Module.End.mul_apply, ← hpi, ← he, ← hphi]
    have h3 := LinearMap.congr_fun h0 (w : S.WL j)
    rw [Module.End.mul_apply, Module.End.mul_apply] at h3
    rw [h3, LinearMap.zero_apply, map_zero]
  set f := phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b with hfdef
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.zero_apply]
  change KT D T i b ⊗[S.Ks] ↥(WKr D S j) at y
  induction y using TensorProduct.induction_on with
  | zero => exact f.map_zero
  | tmul c w =>
    have hcw : (c ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) =
        (c : FractionRing (T.O i)) • ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hcw]
    exact (f.map_smul (c : FractionRing (T.O i))
      (show FmT D T S i j b from ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)))).trans
      (by rw [key]; exact smul_zero _)
  | add y z hy hz =>
    exact (f.map_add (show FmT D T S i j b from y) (show FmT D T S i j b from z)).trans (by rw [hy, hz, add_zero])

end GlobalTheory.HeightCounting.FormsStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualUpperTriangularEigenvectoStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highestWeight_doubleDual_upperTriangular_eigenvector : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (K : Type) [Field K] [CharZero K] (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb →
    ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu →
      ∃ w : Formalism.L2.DIV.Pol K ι n, w ∈ Formalism.L2.DIV.VV K lam ∧ w ≠ 0 ∧
        ∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
          Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) w =
            ((detPow K n B (lam τ₀).detShift)⁻¹ * ∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • w := by
  first | exact @GlobalTheory.AlgWtF.DDHwT.hw_eigvec_transport | exact GlobalTheory.AlgWtF.DDHwT.hw_eigvec_transport | (intros; apply GlobalTheory.AlgWtF.DDHwT.hw_eigvec_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdxVanishOffFinite
section
noncomputable section

namespace GlobalTheory.Mem.IdxFin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

theorem exists_unif {R V : Type} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V] (A B : Submodule R V)
    (hA : A.FG) (h : ∀ x ∈ A, ∃ s : R, s ≠ 0 ∧ s • x ∈ B) : ∃ s : R, s ≠ 0 ∧ ∀ x ∈ A, s • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! f hf using h
  refine ⟨∏ y ∈ S, f y, Finset.prod_ne_zero_iff.2 fun y hy => (hf y (Submodule.subset_span hy)).1, fun x hx => ?_⟩
  have : Submodule.span R (S : Set V) ≤ B.comap ((∏ y ∈ S, f y) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    show (∏ y ∈ S, f y) • y ∈ B
    rw [← Finset.prod_erase_mul S f hy, mul_smul]
    exact B.smul_mem _ (hf y (Submodule.subset_span hy)).2
  exact this hx

theorem locLen_finite {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A C : Submodule (𝓞 K) V) (hA : A.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.locLen w.asIdeal A C ≠ 0}.Finite := by
  by_cases h : ∀ x ∈ A, ∃ s : 𝓞 K, s ≠ 0 ∧ s • x ∈ C
  · obtain ⟨s, hs, hC⟩ := exists_unif A C hA h
    have hf := Ideal.finite_factors (I := Ideal.span {s}) (by simpa using hs)
    refine hf.subset fun w hw => ?_
    by_contra hn
    have hsw : s ∉ w.asIdeal := fun h => hn (Ideal.dvd_span_singleton.2 h)
    have : (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨x, t, ht, hx⟩ -
      exact ⟨s * t, Submonoid.mul_mem _ hsw ht, by rw [mul_smul]; exact hC _ hx⟩
    apply hw
    unfold Formalism.HermitianLatticesTheory.locLen
    rw [this]
    simp [Module.length_eq_zero]
  · push Not at h
    obtain ⟨x, hx, hxC⟩ := h
    refine Set.Finite.subset Set.finite_empty fun w hw => hw ?_
    unfold Formalism.HermitianLatticesTheory.locLen
    have hxA : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A := ⟨1, Submonoid.one_mem _, by simpa using hx⟩
    let φ : 𝓞 K →ₗ[𝓞 K] ((Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A) ⧸
        (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype) :=
      LinearMap.toSpanSingleton _ _ (Submodule.Quotient.mk ⟨x, hxA⟩)
    have hφ : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro r hr
      by_contra hr0
      have h1 : Submodule.Quotient.mk (p := (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype)
          (r • (⟨x, hxA⟩ : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A)) = 0 := hr
      rw [Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨t, ht, h2⟩ := h1
      refine hxC (t * r) (mul_ne_zero (fun h0 => ht (h0 ▸ w.asIdeal.zero_mem)) hr0) ?_
      rw [mul_smul]
      exact h2
    have hle := Module.length_le_of_injective φ hφ
    have htop : Module.length (𝓞 K) (𝓞 K) = ⊤ := by
      by_contra hne
      have hfl := Module.length_ne_top_iff.1 hne
      have hart : IsArtinianRing (𝓞 K) := (isFiniteLength_iff_isNoetherian_isArtinian.1 hfl).2
      exact RingOfIntegers.not_isField K (IsArtinianRing.isField_of_isDomain _)
    rw [htop, top_le_iff] at hle
    rw [hle]
    rfl

theorem lidx_finite {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A B : Submodule (𝓞 K) V) (hA : A.FG) (hB : B.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.lidx w.asIdeal A B ≠ 0}.Finite := by
  refine ((locLen_finite A (A ⊓ B) hA).union (locLen_finite B (A ⊓ B) hB)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
  apply hw
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [hn.1, hn.2]
  simp

theorem jMt_inj (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  have hli := (D.what₂.jMt_basis μ j (Module.Free.chooseBasis _ _)).1
  have := hli.finite
  have := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  exact inj_of_li D.what₂.embLL (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _) hli

theorem TjL_fg (D : D7) (μ : D.what₂.Tup) (j : ℕ)
    (h : ∀ x : D.what₂.MtL μ j,
      ∃ y, D.what₂.jMt μ j y = D.what₂.eMt μ j ((D.what₂.Zj μ j).starProjection (D.what₂.jMt μ j x))) :
    (Idx.TjL D μ j).FG := by
  classical
  choose f hf using h
  choose! g hg using D.what₂.MtLat_sub μ j
  refine Submodule.FG.of_le (Submodule.fg_span
    (((D.what₂.MtLat μ j).gen.finite_toSet.image fun v => f (g v)))) ?_
  rw [Idx.TjL, Submodule.span_le]
  rintro x ⟨_, ⟨c, rfl⟩, hx⟩
  have : x = ∑ v ∈ (D.what₂.MtLat μ j).gen,
      (⟨D.what₂.OtoLL (c v), D.O_int _⟩ : 𝓞 D.what₂.LL) • f (g v) := by
    apply jMt_inj D μ j
    rw [← hx]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun v hv => ?_
    show _ = D.what₂.jMt μ j (D.what₂.OtoLL (c v) • f (g v))
    rw [LinearMap.map_smulₛₗ, hf, hg v hv]
    rfl
  rw [this]
  exact Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, hv, rfl⟩)

theorem thImg_fg {D : D7} (X : DivX D) (μ : D.what₂.Tup) (j : ℕ)
    (A : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j)) (hA : A.FG) : (Idx.thImg X μ j A).FG := by
  let C : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j × (X.MjH j).V) :=
    { carrier := {p | p.1 ∈ A ∧ X.jM j p.2 = D.what₂.thetaP μ j (D.what₂.jMt μ j p.1)}
      add_mem' := by
        rintro a b ⟨hx, h1⟩ ⟨hy, h2⟩
        exact ⟨A.add_mem hx hy, by rw [Prod.fst_add, Prod.snd_add, map_add, map_add, map_add, h1, h2]⟩
      zero_mem' := ⟨A.zero_mem, by simp⟩
      smul_mem' := by
        rintro s a ⟨hx, h1⟩
        refine ⟨A.smul_mem s hx, ?_⟩
        rw [Prod.smul_fst, Prod.smul_snd, Idx.smul_def, ← algebraMap_smul D.what₂.LL s a.2, LinearMap.map_smulₛₗ,
          LinearMap.map_smulₛₗ, h1, LinearMap.map_smul] }
  have hAf : Module.Finite (𝓞 D.what₂.LL) A := Module.Finite.iff_fg.2 hA
  let φ : C →ₗ[𝓞 D.what₂.LL] A :=
    LinearMap.codRestrict A ((LinearMap.fst _ _ _).comp C.subtype) fun p => p.2.1
  have hφ : Function.Injective φ := by
    intro p q hpq
    have h1 : p.1.1 = q.1.1 := congrArg Subtype.val hpq
    exact Subtype.ext (Prod.ext h1 (Idx.jM_inj X j (by rw [p.2.2, q.2.2, h1])))
  have hC : C.FG := Module.Finite.iff_fg.1 (Module.Finite.of_injective φ hφ)
  refine (hC.map (LinearMap.snd _ _ _)).of_le ?_
  rintro y ⟨x, hx, hy⟩
  exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩

theorem jw_finite {D : D7} (j : ℕ) (hfg : (Idx.TjL D D.what₂.mu0 j).FG) :
    {w | Idx.jwIdx D D.what₂.mu0 j w ≠ 0}.Finite := by
  classical
  obtain ⟨S, hS⟩ := id hfg
  have hSm : ∀ a ∈ S, a ∈ Idx.TjL D D.what₂.mu0 j := fun a ha => hS ▸ Submodule.subset_span ha
  have hB : (Idx.TjDual D D.what₂.mu0 j).FG := by
    choose g hg using fun (x : Idx.TjDual D D.what₂.mu0 j) (a : S) => x.2.2 a (hSm a a.2)
    have inj : ∀ c d : 𝓞 D.what₂.LL, D.what₂.embLL (c : D.what₂.LL) = D.what₂.embLL (d : D.what₂.LL) → c = d :=
      fun c d h => RingOfIntegers.ext (D.what₂.embLL.injective h)
    let φ : Idx.TjDual D D.what₂.mu0 j →ₗ[𝓞 D.what₂.LL] (S → 𝓞 D.what₂.LL) :=
      { toFun := g
        map_add' := fun x y => funext fun a => inj _ _ (by
          rw [← hg, Submodule.coe_add, map_add, inner_add_right, hg, hg]; simp)
        map_smul' := fun s x => funext fun a => inj _ _ (by
          rw [← hg, Submodule.coe_smul, Idx.smul_def, LinearMap.map_smulₛₗ, inner_smul_right, hg]; simp) }
    have hφ : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have h0 : ∀ a ∈ S, inner ℂ (D.what₂.jMt D.what₂.mu0 j a) (D.what₂.jMt D.what₂.mu0 j x) = 0 := by
        intro a ha
        rw [hg x ⟨a, ha⟩, show g x ⟨a, ha⟩ = 0 from congrFun hx ⟨a, ha⟩]
        simp
      have hL : ∀ a ∈ Idx.TjL D D.what₂.mu0 j,
          inner ℂ (D.what₂.jMt D.what₂.mu0 j a) (D.what₂.jMt D.what₂.mu0 j x) = 0 := by
        intro a ha
        rw [← hS] at ha
        induction ha using Submodule.span_induction with
        | mem a ha => exact h0 a ha
        | zero => simp
        | add a b _ _ ha hb => rw [map_add, inner_add_left, ha, hb, add_zero]
        | smul s a _ ha => rw [Idx.smul_def, LinearMap.map_smulₛₗ, inner_smul_left, ha, mul_zero]
      have hV : ∀ a ∈ Idx.TjV D D.what₂.mu0 j,
          inner ℂ (D.what₂.jMt D.what₂.mu0 j a) (D.what₂.jMt D.what₂.mu0 j x) = 0 := by
        intro a ha
        induction ha using Submodule.span_induction with
        | mem a ha => exact hL a ha
        | zero => simp
        | add a b _ _ ha hb => rw [map_add, inner_add_left, ha, hb, add_zero]
        | smul s a _ ha => rw [LinearMap.map_smulₛₗ, inner_smul_left, ha, mul_zero]
      have hz := inner_self_eq_zero.1 (hV x x.2.1)
      let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL D.what₂.mu0 j)
      have : Fintype (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL D.what₂.mu0 j)) :=
        @Fintype.ofFinite _ (D.what₂.jMt_basis _ j b).1.finite
      have hinj : Function.Injective (D.what₂.jMt D.what₂.mu0 j) :=
        inj_of_li D.what₂.embLL (D.what₂.jMt D.what₂.mu0 j) b (D.what₂.jMt_basis _ j b).1
      exact Subtype.ext (hinj (by rw [hz]; simp))
    exact Module.Finite.iff_fg.1 (Module.Finite.of_injective φ hφ)
  have := lidx_finite (Idx.TjL D D.what₂.mu0 j) (Idx.TjDual D D.what₂.mu0 j) hfg hB
  exact this.preimage D.plEq.injective.injOn

theorem idx_vanish_off_finite : ∀ (D : D7) (X : DivX D), IdxDefs D X → Idx.HermRat D → Idx.PrRat D → ∃ P : Finset ℕ, ∀ w, D.what₂.places.resChar w ∉ P → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Ij D.what₂.mu0 j w = 0 ∧ D.what₂.jw D.what₂.mu0 j w = 0 := by
  intro D X hI _ hP
  classical
  have hN : ∀ j ∈ Set.Icc 1 D.R.m,
      ({w | Idx.IjIdx X D.what₂.mu0 j w ≠ 0} ∪ {w | Idx.jwIdx D D.what₂.mu0 j w ≠ 0}).Finite := by
    intro j hj
    have hfg := TjL_fg D D.what₂.mu0 j (hP _ j hj.1 hj.2)
    refine Set.Finite.union ?_ (jw_finite j hfg)
    exact (lidx_finite (X.MjH j).L (Idx.thTj X D.what₂.mu0 j) (X.MjH_good j).2.1
      (thImg_fg X _ j _ hfg)).preimage D.plEq.injective.injOn
  have hf := ((Set.finite_Icc 1 D.R.m).biUnion hN).image D.what₂.places.resChar
  refine ⟨hf.toFinset, fun w hw j h1 h2 => ?_⟩
  rw [hI.Ij_def _ j w h1 h2, hI.jw_def _ j w h1 h2]
  by_contra hn
  rw [not_and_or] at hn
  exact hw (hf.mem_toFinset.2 ⟨w, Set.mem_biUnion (x := j) ⟨h1, h2⟩ hn, rfl⟩)

end GlobalTheory.Mem.IdxFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeInIsotypicSupStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_in_isotypic_sup : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool), 1 ≤ j → j ≤ D.R.m →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          V0T D T S In.rho In.chi In.θ i j b ⊓
            ⨅ (k : ℕ) (P : PlE D.host) (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ T.S0 i),
              Module.End.eigenspace (hkT D T S In i j b k P)
                (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.goodPart_le_iSup_eigen | exact GlobalTheory.HeightCounting.FormsStep.goodPart_le_iSup_eigen | (intros; apply GlobalTheory.HeightCounting.FormsStep.goodPart_le_iSup_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPointsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_of_valuation_bounded_at_points : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (N : TrueGeo.Model Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X → haveI := N.ar.isIntegral; ∀ (U : N.X.Opens) (f : N.X.functionField), (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ N.X), spMap e.O.subtype ≫ yt = y.1 ≫ N.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (valAt (y.1 ≫ N.j) f) ≤ 1) → ∀ x ∈ U, RegAt x f := by
  first | exact @GlobalTheory.TrueGeo.RegCrit.regAt_of_integral_values | exact GlobalTheory.TrueGeo.RegCrit.regAt_of_integral_values | (intros; apply GlobalTheory.TrueGeo.RegCrit.regAt_of_integral_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOneMemOfIsRayFieldIn
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.RayRoots

theorem rootOne_mem_of_isRayFieldIn : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (φ : E →+* ℂ)
    (N n : ℕ) (M : IntermediateField ℚ ℂ), N ≠ 0 → n ∣ N → IsRayFieldIn φ (natIdeal E N) M → rootOne n ∈ M :=
  fun _ _ _ _ φ _ _ _ hN hn hM => GlobalTheory.Mem.FieldsEx.rootOne_mem_ray φ hN hn hM

end GlobalTheory.Mem.RayRoots
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L), ∃ σ, IsLocS π.S s σ ∧ ∀ (π' : NG.AutRep L n) (s' : SplitPlace L) (h : s'.w = s.w) σ', π.Iso π' → IsLocS π'.S s' σ' → HEq σ'.cl σ.cl := by
  first | exact @GlobalTheory.LocCompSplit.main | exact GlobalTheory.LocCompSplit.main | (intros; apply GlobalTheory.LocCompSplit.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerListProductMemChernCoefficientRealSpanStatement
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tracePowerListProduct_mem_chernCoefficientRealSpan : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (l : List (ι × ℕ)), (∀ x ∈ l, 1 ≤ x.2) → (l.map Prod.snd).sum = n → (fun A : Mat m S => trProd l A) ∈ Reach m n S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach | exact GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach | (intros; apply GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach <;> assumption)
end

