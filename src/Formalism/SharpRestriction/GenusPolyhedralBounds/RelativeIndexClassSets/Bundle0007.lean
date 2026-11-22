import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0006
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocalFormOfWeakForm
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevelsQDesc

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def ShareRhoT (T rz rq d : ℕ) : Prop := (rz : ℝ) ≤ rq + 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def flipOneThree (D : D7) (nW : ℕ) : ℝ :=
  max (16200 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4)
    (max ((2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 * (nW : ℝ) + 2 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 3)
      ((D.R.r : ℝ) * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 3))

def PageSupp (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) {j : ℕ} (C2 A2 : ℝ) (nW : ℕ) (S : Scal B) (wL : WeightFamilies.Wt D j) :
    Prop :=
  flipOneThree D nW ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  (∀ σ : B.KO →+* ℂ, (DF wL : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ Real.log ‖σ (S.sW : B.KO)‖) ∧
  (D.R.f : ℝ) ^ 2 ≤ D.host.rdE ∧ 8 ≤ D.R.r ∧ 3 ≤ DF wL

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def CombBound4 (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (S : Scal B) (c : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    Prop :=
  ∀ la (ζ : PtsG G la),
    0 ≤ X.vAt la ((Qf la).y ζ) (X.inc _ G.et) ∧ (X.vAt la ((Qf la).y ζ) (X.inc _ G.et) ≠ ⊤ →
      X.depth S.sW wL la ((Qf la).y ζ) ≤
        (((nus la : ℝ) + c / (2 * (G.iet : ℝ)) * (X.vAt la ((Qf la).y ζ) (X.inc _ G.et)).toReal : ℝ) : EReal))

theorem combBound4_of {G : GlobalFamilyData X ka wL wF} {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hj : j < D.R.m) (h : CombBound G S c nus) (Qf : ∀ la, LocalPointData G la) : CombBound4 G Qf S c nus :=
  fun la ζ => (h la ((Qf la).y ζ)).1 hj

def DepthAtM (X : PJ D B P j) (S : Scal B) (wL : WeightFamilies.Wt D j) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  ∀ la (y : X.Pt la), X.depth S.sW wL la y ≤ ((nus la : ℝ) : EReal)

theorem depthAtM_of {G : GlobalFamilyData X ka wL wF} {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hj : D.R.m ≤ j) (h : CombBound G S c nus) : DepthAtM X S wL nus :=
  fun la y => (h la y).2 hj

def ConclAtM (large₂ : SizeData₂ D) (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  D.R.m ≤ j → DepthAtM X S wL nus →
    Concl X S ka wL wF T nus (X.rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

def PageGd4 (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (large₂ : SizeData₂ D) (CG AG Pd : ℝ) : Prop :=
  WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) ≤ Pd

theorem pageGd4_iff {X : PJ D B P j} {ka : WeightFamilies.Wt D j} {large₂ : SizeData₂ D} {CG AG Pd : ℝ} :
    PageGd4 X ka large₂ CG AG Pd ↔ PageGd X ka large₂ CG AG Pd := Iff.rfl

def PolyDom4 (D : D7) {j : ℕ} (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (C2 A2 CR Ch Ah Cq Aq : ℝ)
    (Gc PH Prw Pet Pd : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  2 ≤ K.CRm ∧ 0 ≤ CR ∧ 0 ≤ Gc ∧ 0 ≤ Prw ∧ 0 ≤ WeightFamilies.PP0v D large₂ K.CL K.AL ∧ WeightFamilies.Obound B large₂ Ch Ah ∧
  WeightFamilies.RRv D H.CRc * WeightFamilies.PPv D large₂ H.Cc H.Ac ≤ WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ∧
  WeightFamilies.RRv D K.CRm * D.host.rdE ^ 2 ≤ WeightFamilies.RRv D CR ^ 2 ∧
  2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 ∧ 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f ∧
  (2 * Gc + 6 * PH + Prw) * 25 ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  Pet ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂) ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  60 * Gc + 180 * PH + 44 * (2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) +
      22 * (2 * WeightFamilies.PPv D large₂ Cq Aq) ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * (WeightFamilies.dimY D j : ℝ) ∧
  1 / 2 ≤ Prw ∧ Prw ≤ PH ∧ 0 ≤ Pet ∧
  Prw ≤ WeightFamilies.PPv D large₂ C2 A2

theorem polyDom4_iff {B : WeightFamilies.Prov D} {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd : ℝ}
    {ka : WeightFamilies.Wt D j} :
    PolyDom4 D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka ↔ PolyDom D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka :=
  Iff.rfl

def Conclusion1OfComb4 : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → PageSupp D large₂ B C2 A2 nW S wL →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd4 (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoT (D := D) (j := j) T G.rz G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom4 (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    (∀ la, InContainZ G la S T) → (∀ la, InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL)) →
    (j < D.R.m → ∃ Qf : ∀ la, LocalPointData G la,
      (∀ la, InBasis G la) ∧ (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S Gc Prw T) ∧
      CombBound4 G Qf S (cc D large₂ C2 A2 CR wL) nus ∧ Heights Qf Gc PH Prw Pet) →
    (D.R.m ≤ j → DepthAtM (X j h1 h2) S wL nus) →
    ConclAtM large₂ (X j h1 h2) S ka wL wF T nus →
    Concl (X j h1 h2) S ka wL wF T nus
      ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsGlobalFamilyQuotientBounded
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

section LinAlgQ

theorem exists_den {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (M : Submodule R V)
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V) : ∃ s ∈ nonZeroDivisors R, s • v ∈ M := by
  have hv : v ∈ Submodule.span K (M : Set V) := by rw [hM]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_mem _, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    have h1 : (s * t) • x = t • (s • x) := by rw [mul_comm, mul_smul]
    rw [smul_add, h1, mul_smul]
    exact M.add_mem (M.smul_mem _ hsx) (M.smul_mem _ hty)
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective R a
    refine ⟨d * s, mul_mem hd hs, ?_⟩
    have hd0 : algebraMap R K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hd)
    have h1 : (d * s) • ((algebraMap R K n / algebraMap R K d) • x) = n • (s • x) := by
      rw [← algebraMap_smul K (d * s), ← algebraMap_smul K n, ← algebraMap_smul K s, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [h1]
    exact M.smul_mem _ hsx

theorem finrank_quot_eq {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (M : Submodule R V)
    (hM : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V) :
    finrank R (M ⧸ (W.restrictScalars R).comap M.subtype) = finrank K (V ⧸ W) := by
  let g : M →ₗ[R] (V ⧸ W) := (W.mkQ.restrictScalars R).comp M.subtype
  have hker : LinearMap.ker g = (W.restrictScalars R).comap M.subtype := by
    ext x
    simp [g]
  let f : (M ⧸ (W.restrictScalars R).comap M.subtype) →ₗ[R] (V ⧸ W) :=
    Submodule.liftQ _ g (le_of_eq hker.symm)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hker)
  have hloc : IsLocalizedModule (nonZeroDivisors R) f := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, by rw [hinj h]⟩⟩
    · have hs0 : algebraMap R K s ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero s.2)
      rw [Module.End.isUnit_iff]
      constructor
      · intro a b hab
        simp only [Module.algebraMap_end_apply] at hab
        rw [← algebraMap_smul K (s : R) a, ← algebraMap_smul K (s : R) b] at hab
        exact smul_right_injective _ hs0 hab
      · intro a
        refine ⟨(algebraMap R K s)⁻¹ • a, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul K (s : R), smul_smul, mul_inv_cancel₀ hs0, one_smul]
    · obtain ⟨v, rfl⟩ := W.mkQ_surjective y
      obtain ⟨s, hs, hsv⟩ := exists_den (K := K) M hM v
      refine ⟨(Submodule.Quotient.mk ⟨s • v, hsv⟩, ⟨s, hs⟩), ?_⟩
      rfl
  rw [IsLocalization.finrank_eq K (nonZeroDivisors R) le_rfl, IsLocalizedModule.finrank_eq (nonZeroDivisors R) f le_rfl]

theorem exists_sub_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Sh : Finset V) (hS : Submodule.span K (Sh : Set V) = ⊤) (W : Submodule K V) :
    ∃ e : Fin (finrank K (V ⧸ W)) → V, (∀ i, e i ∈ Sh) ∧ Submodule.span K (Set.range e) ⊔ W = ⊤ := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (W.mkQ '' (Sh : Set V))
  have htop : Submodule.span K b = ⊤ := by
    rw [hspan, Submodule.span_image, hS, Submodule.map_top, Submodule.range_mkQ]
  have hfin : Finite b := ((Sh.finite_toSet.image _).subset hb).to_subtype
  have := Fintype.ofFinite b
  let bs : Basis b K (V ⧸ W) := Basis.mk hli (by rw [Subtype.range_coe, htop])
  have hcard : Fintype.card b = finrank K (V ⧸ W) := (finrank_eq_card_basis bs).symm
  let eq : Fin (finrank K (V ⧸ W)) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hpre : ∀ k, ∃ v ∈ (Sh : Set V), W.mkQ v = (eq k : V ⧸ W) := fun k => hb (eq k).2
  choose e he1 he2 using hpre
  refine ⟨e, fun i => he1 i, ?_⟩
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
  have : (⇑W.mkQ ∘ e) = (Subtype.val : b → V ⧸ W) ∘ eq := by funext k; exact he2 k
  rw [this, Set.range_comp, eq.surjective.range_eq, Set.image_univ, Subtype.range_coe, htop]

end LinAlgQ

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem rhoP_eq_finrank (B : WeightFamilies.Prov D) (CR T c : ℝ) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (hM : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤) :
    WeightFamilies.rhoP B CR T c j ka = finrank B.KO (B.Cusp j ka ⧸ WeightFamilies.MggK B CR T c j ka) :=
  finrank_quot_eq (B.Mlat j ka) hM (WeightFamilies.MggK B CR T c j ka)

theorem exists_global_family_quotient_bounded {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G0 : GlobalFamilyData X ka wL wF) (large₂ : SizeData₂ D) (S : Scal B)
    (CRm : ℝ) (T : ℕ) (c be Ch Ah : ℝ)
    (hS4 : ShortG X ka (X.Thc S.sK ka) be)
    (hM : X.Thc S.sK ka ≤ B.Mlat j ka)
    (hbe : be ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) :
    ∃ th : Fin (WeightFamilies.rhoP B CRm T c j ka) → B.Mlat j ka,
      ({ G0 with rq := WeightFamilies.rhoP B CRm T c j ka, th := th } : GlobalFamilyData X ka wL wF).TiedQ large₂ S CRm T c Ch Ah := by
  obtain ⟨Sh, hSh, hspan, hshort⟩ := hS4
  have hMtop : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤ :=
    top_le_iff.mp (hspan ▸ Submodule.span_mono fun x hx => hM (hSh hx))
  have hex := exists_sub_basis Sh hspan (WeightFamilies.MggK B CRm T c j ka)
  rw [← rhoP_eq_finrank B CRm T c j ka hMtop] at hex
  obtain ⟨e, he, hsup⟩ := hex
  exact ⟨fun i => ⟨e i, hM (hSh (he i))⟩, rfl, fun i => hSh (he i), hsup, fun i => (hshort _ (he i)).trans hbe⟩

theorem exists_global_family_quotient {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G0 : GlobalFamilyData X ka wL wF) (large₂ : SizeData₂ D) (S : Scal B)
    (CRm : ℝ) (T : ℕ) (c Gc Ch Ah : ℝ)
    (hS4 : ShortG X ka (X.Thc S.sK ka) (Gc * ka.size))
    (hM : X.Thc S.sK ka ≤ B.Mlat j ka)
    (hG : Gc ≤ WeightFamilies.PPv D large₂ Ch Ah) :
    ∃ (rq : ℕ) (th : Fin rq → B.Mlat j ka),
      ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF).TiedQ large₂ S CRm T c Ch Ah :=
  ⟨_, exists_global_family_quotient_bounded G0 large₂ S CRm T c (Gc * ka.size) Ch Ah hS4 hM
    (mul_le_mul_of_nonneg_right hG (by linarith [ka.one_le_size]))⟩

section Unchanged

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G0 : GlobalFamilyData X ka wL wF) (rq : ℕ) (th : Fin rq → B.Mlat j ka)

example : ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) =
    ⟨G0.N, G0.w, G0.del, G0.th', G0.rz, G0.alz, G0.th0, G0.zc, rq, th, G0.iet, G0.et, G0.mx⟩ := rfl

theorem tiedW_reQ (S : Scal B) (Gc Prw : ℝ) :
    ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF).TiedW S Gc Prw ↔ G0.TiedW S Gc Prw := Iff.rfl

theorem tiedTh_reQ (S : Scal B) (Gc : ℝ) :
    ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF).TiedTh S Gc ↔ G0.TiedTh S Gc := Iff.rfl

theorem tiedZ_reQ (S : Scal B) (T : ℕ) (Gc : ℝ) :
    ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF).TiedZ S T Gc ↔ G0.TiedZ S T Gc := Iff.rfl

theorem tiedEt_reQ (large₂ : SizeData₂ D) (Cf Af : ℝ) :
    ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF).TiedEt large₂ Cf Af ↔ G0.TiedEt large₂ Cf Af := Iff.rfl

theorem inBasis_reQ (la : HeightOneSpectrum (𝓞 B.KO)) :
    InBasis ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) la ↔ InBasis G0 la := Iff.rfl

theorem inContainZ_reQ (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (T : ℕ) :
    InContainZ ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) la S T ↔ InContainZ G0 la S T := Iff.rfl

theorem inContainM_reQ (la : HeightOneSpectrum (𝓞 B.KO)) (CRm : ℝ) (T : ℕ) (c : ℝ) :
    InContainM ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) la CRm T c ↔ InContainM G0 la CRm T c := Iff.rfl

theorem combBound_reQ (S : Scal B) (c : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    CombBound ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) S c nus ↔ CombBound G0 S c nus := Iff.rfl

example (la : HeightOneSpectrum (𝓞 B.KO)) :
    PtsG ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) la = PtsG G0 la := rfl

def LocalPointData.reQ {G0 : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G0 la) (rq : ℕ) (th : Fin rq → B.Mlat j ka) :
    LocalPointData ({ G0 with rq := rq, th := th } : GlobalFamilyData X ka wL wF) la :=
  ⟨Q.y, Q.g0, Q.c⟩

variable {G0} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G0 la)

theorem LocalPointData.inCurve_reQ : (Q.reQ rq th).InCurve ↔ Q.InCurve := Iff.rfl

theorem LocalPointData.inTie_reQ (S : Scal B) : (Q.reQ rq th).InTie S ↔ Q.InTie S := Iff.rfl

theorem LocalPointData.inLift_reQ (T : ℕ) : (Q.reQ rq th).InLift T ↔ Q.InLift T := Iff.rfl

theorem heights_reQ (Qf : ∀ la, LocalPointData G0 la) (Gc PH Prw Pet : ℝ) :
    Heights (fun la => (Qf la).reQ rq th) Gc PH Prw Pet ↔ Heights Qf Gc PH Prw Pet := Iff.rfl

end Unchanged

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IsLatticeOfAdmissible
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.T0

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem qlen_of_idx (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (la : HeightOneSpectrum (𝓞 B.KO))
    (hLat : InLat X ka la S wL wF T) (hΘM : X.Theta S ka wL wF T ≤ X.Msup ka) (e r : ℝ)
    (h : ∀ U : Submodule (X.Kl la) ↥(WL X ka la),
      (Formalism.LatticeIndexTer.idx (X.Ol la) ↥(WL X ka la) (MW X ka la ⊓ U.restrictScalars (X.Ol la))
        (ThW X S ka wL wF T la ⊓ U.restrictScalars (X.Ol la)) : ℝ) ≤ e * (finrank (X.Kl la) U : ℝ) + r)
    (V' : Submodule (X.Kl la) (X.Vl la)) (hV' : V' ≤ X.locK la (X.Msup ka)) :
    X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
      ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
        (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤ e * (finrank (X.Kl la) V' : ℝ) + r := by
  have hb := h (V'.comap (WL X ka la).subtype)
  have hrk : finrank (X.Kl la) ↥(V'.comap (WL X ka la).subtype) = finrank (X.Kl la) V' :=
    (Submodule.comapSubtypeEquivOfLe hV').finrank_eq
  have hq := qlen_eq_inW X ka la (X.loc la (X.Msup ka)) (X.loc la (X.Theta S ka wL wF T)) V' hV'
  have hle : ThW X S ka wL wF T la ≤ MW X ka la :=
    Submodule.comap_mono (Submodule.span_mono (Set.image_mono hΘM))
  have h0 := qlen_eq_zero_of_le
    (MW X ka la ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
    (ThW X S ka wL wF T la ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
    (inf_le_inf_right _ hle)
  have hfin := qlen_inf_ne_top (X.Ol la) (X.Kl la) ↥(WL X ka la) (MW X ka la) (ThW X S ka wL wF T la)
    hLat.1 hLat.2 ((V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
  rw [← hq]
  refine ⟨hfin, ?_⟩
  rw [hrk] at hb
  unfold Formalism.LatticeIndexTer.idx at hb
  rw [h0] at hb
  have hb' := hb
  simp only [ENat.toNat_zero, Nat.cast_zero, sub_zero, Int.cast_natCast] at hb'
  exact hb'

theorem qlen_of_idx_of_hyp {large₂ : SizeData₂ D} (X : PJ D B P j) {H : KHyp} {C2 A2 CR Bx CT : ℝ} (S : Scal B)
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hH : Hyp large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) (la : HeightOneSpectrum (𝓞 B.KO))
    (hLat : InLat X ka la S wL wF T) (e r : ℝ)
    (h : ∀ U : Submodule (X.Kl la) ↥(WL X ka la),
      (Formalism.LatticeIndexTer.idx (X.Ol la) ↥(WL X ka la) (MW X ka la ⊓ U.restrictScalars (X.Ol la))
        (ThW X S ka wL wF T la ⊓ U.restrictScalars (X.Ol la)) : ℝ) ≤ e * (finrank (X.Kl la) U : ℝ) + r)
    (V' : Submodule (X.Kl la) (X.Vl la)) (hV' : V' ≤ X.locK la (X.Msup ka)) :
    X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
      ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
        (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤ e * (finrank (X.Kl la) V' : ℝ) + r :=
  qlen_of_idx X S ka wL wF T la hLat (theta_le_msup_of_hyp X S hH) e r h V' hV'

theorem isLattice_of_admissible (h : WeightAlgebra.adm1 B) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka : WeightFamilies.Wt D j) :
    Submodule.IsLattice B.KO (B.Mlat j ka) := h j h1 h2 ka

theorem span_eq_top_of_shortG {X : PJ D B P j} {w : WeightFamilies.Wt D j} {N : Submodule (𝓞 B.KO) (B.Cusp j w)} {β : ℝ}
    (h : ShortG X w N β) : Submodule.span B.KO (N : Set (B.Cusp j w)) = ⊤ := by
  obtain ⟨Sh, h1, h2, -⟩ := h
  exact top_le_iff.1 (h2 ▸ Submodule.span_mono h1)

theorem span_Thc_of_hyp {large₂ : SizeData₂ D} {X : PJ D B P j} {H : KHyp} {C2 A2 CR Bx CT : ℝ} {S : Scal B}
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hH : Hyp large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) :
    Submodule.span B.KO (X.Thc S.sF wF : Set (B.Cusp j wF)) = ⊤ ∧
    Submodule.span B.KO (X.Thc S.s0 (X.wF0 wL wF) : Set (B.Cusp j (X.wF0 wL wF))) = ⊤ ∧
    Submodule.span B.KO (X.Thc S.sK ka : Set (B.Cusp j ka)) = ⊤ := by
  obtain ⟨-, -, ⟨-, -, -, -, -, po, -, -, PLam, -, -, hF, h0', hK⟩, -⟩ := hH
  exact ⟨span_eq_top_of_shortG hF, span_eq_top_of_shortG h0', span_eq_top_of_shortG hK⟩

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SectionMonomialGenerators
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Base

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (ka : WeightFamilies.Wt D j)

theorem bcV_mem_Vw {x : X.Vl la} (hx : x ∈ T0.WL X ka la) : bcV X la N x ∈ Vw X la N ka := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, ⟨F', _, rfl⟩, rfl⟩ := hx
    exact emb_mem_Vw X la N ka F'
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_smul, ← algebraMap_smul (Kp X la N) a]
    exact Submodule.smul_mem _ _ hx

def jW : ↥(T0.WL X ka la) →ₗ[X.Kl la] ↥(Vw X la N ka) :=
  ((bcV X la N).toLinearMap.domRestrict (T0.WL X ka la)).codRestrict ((Vw X la N ka).restrictScalars (X.Kl la))
    fun x => bcV_mem_Vw X la N ka x.2

theorem coe_jW (x : ↥(T0.WL X ka la)) : (jW X la N ka x : Rp X la N) = bcV X la N (x : X.Vl la) := rfl

def M1 : Submodule (Op X la N) ↥(Vw X la N ka) :=
  Submodule.span (Op X la N) (jW X la N ka '' (T0.MW X ka la : Set ↥(T0.WL X ka la)))

def Th1 (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T : ℕ) : Submodule (Op X la N) ↥(Vw X la N ka) :=
  Submodule.span (Op X la N) (jW X la N ka '' (T0.ThW X S ka wL wF T la : Set ↥(T0.WL X ka la)))

def MggO (B : WeightFamilies.Prov D) (CRm T c : ℝ) (j : ℕ) (ka : WeightFamilies.Wt D j) : Submodule (𝓞 B.KO) (B.Cusp j ka) :=
  B.Mlat j ka ⊓ (WeightFamilies.MggK B CRm T c j ka).restrictScalars (𝓞 B.KO)

def MggW (CRm T c : ℝ) : Submodule (X.Ol la) ↥(T0.WL X ka la) :=
  T0.inW X ka la (X.loc la (X.emb ka (MggO B CRm T c j ka)))

def toW (F : B.Mlat j ka) : ↥(T0.WL X ka la) :=
  ⟨X.bc la (X.inc ka F), Submodule.subset_span ⟨X.inc ka F, ⟨F, F.2, rfl⟩, rfl⟩⟩

end Base

section Chain

variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X (addL wF wL T) wL wF)
  (la : HeightOneSpectrum (𝓞 B.KO))

def sectionMonomialGenerators : Set ↥(Vw X la G.N (addL wF wL T)) :=
  {f | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
      (f : Rp X la G.N) = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))}

def N1 : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) := Submodule.span (Op X la G.N) (sectionMonomialGenerators G la)

def Zg : Set ↥(Vw X la G.N (addL wF wL T)) := {f | ∃ k : Fin G.rz, (f : Rp X la G.N) = zK G la k}

def Zl : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) := Submodule.span (Op X la G.N) (Zg G la)

def ZK : Submodule (Kp X la G.N) ↥(Vw X la G.N (addL wF wL T)) := Submodule.span (Kp X la G.N) (Zg G la)

def NovK : Submodule (Kp X la G.N) ↥(Vw X la G.N (addL wF wL T)) :=
  Submodule.span (Kp X la G.N) ((N1 G la ⊔ Zl G la : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T))) :
    Set ↥(Vw X la G.N (addL wF wL T)))

def Zm : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) :=
  M1 X la G.N (addL wF wL T) ⊓ (ZK G la).restrictScalars (Op X la G.N)

def Np (e : ℕ) : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) :=
  ((M1 X la G.N (addL wF wL T)).map ((unifO X la G.N ^ e) •
      (LinearMap.id : ↥(Vw X la G.N (addL wF wL T)) →ₗ[Op X la G.N] ↥(Vw X la G.N (addL wF wL T)))) ⊓
    (NovK G la).restrictScalars (Op X la G.N)) ⊔ N1 G la ⊔ Zm G la

def rhoO : ↥(Vw X la G.N (addL wF wL T)) →ₗ[Op X la G.N] WK X la G.w wF (a0 D j T) :=
  (rhoK X la G.w wF (a0 D j T) T).restrictScalars (Op X la G.N)

def rhoN (e : ℕ) : ↥(Np G la e) →ₗ[Op X la G.N] WK X la G.w wF (a0 D j T) :=
  rhoO G la ∘ₗ (Np G la e).subtype

theorem reducedGenerators_eq_map : firstLength_le_prime_bound G la T = (N1 G la).map (rhoO G la) := by
  unfold firstLength_le_prime_bound N1
  rw [Submodule.map_span]
  rfl

end Chain

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfLocalAndSum
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

theorem concl_of_nat {j : ℕ} (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) (r : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hnu : ∀ la, 0 ≤ nus la) (hr0 : ∀ la, 0 ≤ r la) (hrs : Summable (fun la => r la * X.lN la))
    (hrb : (∑' la, r la * X.lN la) ≤ β)
    (hloc : ∀ la (e : ℕ), (T : ℝ) * nus la ≤ (e : ℝ) →
      ∀ V' : Submodule (X.Kl la) (X.Vl la), V' ≤ X.locK la (X.Msup ka) →
        X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
        ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
            (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤
          (e : ℝ) * (Module.finrank (X.Kl la) V' : ℝ) + r la) :
    Concl X S ka wL wF T nus β := by
  unfold Concl
  refine ⟨r, hr0, hrs, hrb, ?_⟩
  intro la e he V' hV'
  have hT : (0 : ℝ) ≤ (T : ℝ) * nus la := mul_nonneg (Nat.cast_nonneg _) (hnu la)
  have he0 : (0 : ℤ) ≤ e := by
    have h := hT.trans he
    exact_mod_cast h
  lift e to ℕ using he0 with n
  have h := hloc la n (by exact_mod_cast he) V' hV'
  simpa only [Int.cast_natCast] using h

theorem theorem_zero_of_local_and_sum (hL : LocalBoundHypothesis D B P) (hS : SumBoundHypothesis D B P) : Conclusion1Of2 (D := D) (B := B) (P := P) := by
  unfold Conclusion1Of2
  intro large₂ X K H Ch Ah Cq Aq C2 A2 CR CT hA hB hEx j h1 h2 S ka wL wF T nP nW h0 nus hH
  obtain ⟨G, Gc, PH, Prw, Pet, Pd, hT, hD, hSh, hP, Qf, hOk, hHt⟩ := hEx j h1 h2 S ka wL wF T nP nW h0 nus hH
  have hsum := hS large₂ X K H Ch Ah Cq Aq C2 A2 CR CT hA hB j h1 h2 S ka wL wF T nP nW h0 nus hH G Gc PH Prw Pet Pd
    hT hD hSh hP Qf hOk hHt
  have hloc := hL large₂ X K H Ch Ah Cq Aq C2 A2 CR CT hA hB j h1 h2 S ka wL wF T nP nW h0 nus hH G Gc PH Prw Pet Pd
    hT hD hSh hP
  exact concl_of_nat (X j h1 h2) S ka wL wF T nus _ (fun la => rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL))
    hH.2.2.2.1.1 hsum.1 hsum.2.1 hsum.2.2
    (fun la e he V' hV' => hloc la (Qf la) (hOk la) (hHt.1 la) e he V' hV')

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

