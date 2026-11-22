import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdPullbackMulResidueDegreeCodimOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2935
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3078
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebung
section
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDivGroup

theorem finrank_range_relFrob_dual_add_finrank_ker_verschiebung (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (h : (p : k) = 0) (G : PDivGroup p k) : Module.finrank k (LinearMap.range ((relFrob h G.dual).app 1 : (frobTwist h G.dual).A 1 →ₐ[k] G.dual.A 1).toLinearMap) + Module.finrank k (LinearMap.ker ((verschiebung h G).app 1 : G.A 1 →ₐ[k] (frobTwist h G).A 1).toLinearMap) = Module.finrank k (G.A 1) := by
  let e : G.dual.A 1 ≃ₗ[k] Module.Dual k (G.A 1) := CartierDual.toDual k (G.A 1)
  set W := LinearMap.range ((relFrob h G.dual).app 1 : (frobTwist h G.dual).A 1 →ₐ[k] G.dual.A 1).toLinearMap with hW
  have hker : LinearMap.ker ((verschiebung h G).app 1 : G.A 1 →ₐ[k] (frobTwist h G).A 1).toLinearMap
      = (W.map e.toLinearMap).dualCoannihilator := by
    ext a
    rw [Submodule.mem_dualCoannihilator, LinearMap.mem_ker]
    change (verschiebung h G).app 1 a = 0 ↔ _
    constructor
    · rintro ha _ ⟨_, ⟨x, rfl⟩, rfl⟩
      change e ((relFrob h G.dual).app 1 x) a = 0
      induction x using frobTwist_induction h (G := G.dual) 1 with
      | h0 => simp
      | h2 x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, add_zero]
      | h1 r χ =>
        rw [map_smul, map_smul, LinearMap.smul_apply, relFrob_app_frobProj]
        have := frobTwistDual_verschiebung h 1 χ a
        rw [ha, map_zero] at this
        exact (congrArg (r • ·) this.symm).trans (smul_zero r)
    · intro ha
      refine frobTwist_ext_dual h 1 fun χ => ?_
      rw [frobTwistDual_verschiebung, map_zero]
      refine ha _ ⟨_, ⟨(frobProj h G.dual).app 1 χ, rfl⟩, ?_⟩
      exact congrArg e (relFrob_app_frobProj h (G := G.dual) 1 χ)
  rw [hker, ← e.finrank_map_eq W]
  exact Subspace.finrank_add_finrank_dualCoannihilator_eq _

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelQuotientLePowCotangent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.FrobKerDim

theorem finrank_quot_frobKerIdeal_le : ∀ (q : ℕ) (K H : Type) [Field K] [CommRing H] [Bialgebra K H]
    [Module.Finite K H], 0 < q →
    Module.finrank K (H ⧸ frobKerIdeal q K H) ≤ q ^ Module.finrank K (Cot K H) := by
  intro q K H _ _ _ _ hq
  classical
  set J := frobKerIdeal q K H with hJ
  set ε := Bialgebra.counitAlgHom K H with hε
  set mk := Ideal.Quotient.mkₐ K J with hmk
  have hJI : ∀ a ∈ J, ε a = 0 := fun a ha => frobKerIdeal_le_augIdeal hq.ne' K H ha
  set εQ : (H ⧸ J) →ₐ[K] K := Ideal.Quotient.liftₐ J ε hJI with hεQ
  have hεQmk : ∀ a, εQ (mk a) = ε a := fun a => rfl
  have hmks : Function.Surjective mk := Ideal.Quotient.mkₐ_surjective K J
  haveI hfinQ : Module.Finite K (H ⧸ J) := Module.Finite.of_surjective mk.toLinearMap hmks
  haveI : IsNoetherianRing (H ⧸ J) := isNoetherian_of_tower K inferInstance

  have hkerQ : ∀ z ∈ RingHom.ker εQ, ∃ a ∈ RingHom.ker ε, mk a = z := by
    intro z hz
    obtain ⟨a, rfl⟩ := hmks z
    refine ⟨a, ?_, rfl⟩
    rw [RingHom.mem_ker] at hz ⊢
    rw [← hεQmk]; exact hz
  have hpowQ : ∀ z ∈ RingHom.ker εQ, z ^ q = 0 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
  have hnil : IsNilpotent (RingHom.ker εQ) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨q, hpowQ f hf⟩

  haveI : Module.Finite K (AugCot ε) := Module.Finite.of_surjective _ (AugCot.d_surjective ε)
  set d := Module.finrank K (AugCot ε) with hd
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin d → K, AugCot.d ε (∑ i, l i • (x i : H)) = ∑ i, l i • b i := by
    intro l
    simp [map_sum, hx]
  have hmem : ∀ l : Fin d → K, (∑ i, l i • (x i : H)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  have hspanH : ∀ a ∈ RingHom.ker ε, ∃ l : Fin d → K, a - ∑ i, l i • (x i : H) ∈ RingHom.ker ε ^ 2 := by
    intro a ha
    refine ⟨b.repr (AugCot.d ε a), ?_⟩
    have h1 : AugCot.d ε (a - ∑ i, b.repr (AugCot.d ε a) i • (x i : H)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem ha (hmem _)), Ideal.toCotangent_eq_zero] at h1
  let y : Fin d → H ⧸ J := fun i => mk (x i)
  have hy : ∀ i, y i ∈ RingHom.ker εQ := fun i => by
    rw [RingHom.mem_ker, hεQmk]; exact (x i).2
  have hmapI : Ideal.map mk (RingHom.ker ε) ≤ RingHom.ker εQ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact ha
  have hspan : ∀ z ∈ RingHom.ker εQ, ∃ l : Fin d → K, z - ∑ i, l i • y i ∈ RingHom.ker εQ ^ 2 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    obtain ⟨l, hl⟩ := hspanH a ha
    refine ⟨l, ?_⟩
    have h1 : mk (a - ∑ i, l i • (x i : H)) ∈ Ideal.map mk (RingHom.ker ε ^ 2) :=
      Ideal.mem_map_of_mem _ hl
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.pow_right_mono hmapI 2 h1
    simpa [y, map_sub, map_sum, map_smul] using h2
  have hsurj := GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent εQ hnil y hy hspan
  have hyq : ∀ i, y i ^ q = 0 := fun i => hpowQ _ (hy i)

  let mon : (Fin d → Fin q) → H ⧸ J := fun e => ∏ i, y i ^ (e i : ℕ)
  have htop : Submodule.span K (Set.range mon) = ⊤ := by
    have hall : ∀ P : MvPolynomial (Fin d) K, MvPolynomial.aeval y P ∈ Submodule.span K (Set.range mon) := by
      intro P
      induction P using MvPolynomial.induction_on' with
      | monomial u a =>
        rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
          ← Algebra.smul_def]
        refine Submodule.smul_mem _ _ ?_
        by_cases h : ∀ i, u i < q
        · exact Submodule.subset_span ⟨fun i => ⟨u i, h i⟩, rfl⟩
        · push_neg at h
          obtain ⟨i, hi⟩ := h
          have h0 : y i ^ u i = 0 := pow_eq_zero_of_le hi (hyq i)
          rw [Finset.prod_eq_zero (i := i) (Finset.mem_univ i) h0]
          exact Submodule.zero_mem _
      | add P Q hP hQ => rw [map_add]; exact Submodule.add_mem _ hP hQ
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨P, rfl⟩ := hsurj z
    exact hall P
  have h1 := finrank_range_le_card (R := K) (b := mon)
  rw [Set.finrank, htop, finrank_top] at h1
  simpa [Fintype.card_fun, Fintype.card_fin] using h1

end GlobalTheory.FrobKerDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdPullbackMulResidueDegreeCodimOneStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_ord_pullback_mul_residueDegree_codim_one : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (π : Y ⟶ X) (hη : π (genericPoint Y) ⤳ genericPoint X) (z : X), Order.coheight z = 1 → (∃ U : X.Opens, z ∈ U ∧ IsFinite (π ∣_ U)) → ∀ f : X.functionField, f ≠ 0 → ∑ᶠ (w : Y) (_ : π w = z), Scheme.ord (TrueGeo.SmallSec.fnMap π hη f) w * (π.residueDegree w : ℤ) = (π.residueDegree (genericPoint Y) : ℤ) * Scheme.ord f z := by
  first | exact @GlobalTheory.OrdPush.finsum_ord_fnMap_mul_residueDegree | exact GlobalTheory.OrdPush.finsum_ord_fnMap_mul_residueDegree | (intros; apply GlobalTheory.OrdPush.finsum_ord_fnMap_mul_residueDegree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleCarriesBaseChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option autoImplicit false
noncomputable section
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.FlagCell.CellOpen

theorem spans_res {X : Scheme.{0}} {F : X.Modules} {m : ℕ} {fl : Vert.Flag F m} {V W : X.Opens}
    {v : Fin m → Γ(F, V)} (hv : Spans fl V v) (h : W ≤ V) :
    Spans fl W fun j => resM F h (v j) := by
  intro l
  obtain ⟨s, hs, hsv⟩ := hv l
  exact ⟨fun j => resM _ h (s j), hs.res h, fun j => by rw [app_resM, hsv]⟩

theorem res_pullCol {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} {U : B.Opens} {m : ℕ}
    (e : Fin m → Γ(E, U)) {V W : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U) (h : W ≤ V)
    (M : Matrix (Fin m) (Fin m) Γ(Y, V)) (j : Fin m) :
    resM _ h (pullCol π e hV M j) = pullCol π e (h.trans hV) (M.map (resG Y h)) j := by
  simp only [pullCol, map_sum, resM_smul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  exact QCoh.res_pullbackSections π E hV h (e l)

theorem sum_smul_pullCol {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} {U : B.Opens} {m : ℕ}
    (e : Fin m → Γ(E, U)) {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U)
    (N M : Matrix (Fin m) (Fin m) Γ(Y, V)) (j : Fin m) :
    ∑ k, M k j • pullCol π e hV N k = pullCol π e hV (N * M) j := by
  simp only [pullCol, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem isFrame_pullbackSections {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} [E.IsQuasicoherent]
    {U : B.Opens} {m : ℕ} {e : Fin m → Γ(E, U)} (he : IsFrame e) {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U) :
    IsFrame fun l => QCoh.pullbackSections π E hV (e l) := by
  have := (he.pullback π).res hV
  rwa [funext fun i => QCoh.res_pullbackSections π E le_rfl hV (e i)] at this

theorem exists_pullCol {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} [E.IsQuasicoherent]
    {U : B.Opens} {m : ℕ} {e : Fin m → Γ(E, U)} (he : IsFrame e) {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U)
    (v : Fin m → Γ((Scheme.Modules.pullback π).obj E, V)) :
    ∃ M : Matrix (Fin m) (Fin m) Γ(Y, V), ∀ j, v j = pullCol π e hV M j := by
  have hb := isFrame_pullbackSections π he hV V le_rfl
  choose c hc using fun j => hb.2 (v j)
  refine ⟨Matrix.of fun l j => c j l, fun j => ?_⟩
  rw [← hc j, Fintype.linearCombination_apply]
  simp only [pullCol, Matrix.of_apply, resM_self]

theorem pullCol_injective {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} [E.IsQuasicoherent]
    {U : B.Opens} {m : ℕ} {e : Fin m → Γ(E, U)} (he : IsFrame e) {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U)
    {M N : Matrix (Fin m) (Fin m) Γ(Y, V)} (h : ∀ j, pullCol π e hV M j = pullCol π e hV N j) :
    M = N := by
  have hb := isFrame_pullbackSections π he hV V le_rfl
  ext l j
  have := hb.1 (a₁ := fun l => M l j) (a₂ := fun l => N l j) (by
    simp only [Fintype.linearCombination_apply, resM_self]
    exact h j)
  exact congrFun this l

theorem isUnit_minor_of_upper {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (hM : M.BlockTriangular id) (hd : IsUnit M.det) (l : Fin (m + 1)) :
    IsUnit (M.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
  have hM' : (M.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).BlockTriangular id :=
    fun i j hij => hM (show Fin.castLE l.is_le j < Fin.castLE l.is_le i from hij)
  rw [Matrix.det_of_isUpperTriangular hM']
  rw [Matrix.det_of_isUpperTriangular hM] at hd
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => ?_
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun k => M k k) (Finset.mem_univ _)) hd

theorem mem_basicOpen_of_isUnit_appLE {T Y : Scheme.{0}} (g' : T ⟶ Y) {V : Y.Opens} {V' : T.Opens}
    (h : V' ≤ g' ⁻¹ᵁ V) (d : Γ(Y, V)) (hd : IsUnit (g'.appLE V V' h d)) {t : T} (ht : t ∈ V') :
    g' t ∈ Y.basicOpen d := by
  have e := Scheme.basicOpen_appLE g' V' V h d
  rw [T.basicOpen_of_isUnit hd] at e
  have : t ∈ V' ⊓ g' ⁻¹ᵁ Y.basicOpen d := e ▸ ht
  exact this.2

theorem isUnit_resG_of_le_basicOpen {Y : Scheme.{0}} {V W : Y.Opens} (d : Γ(Y, V))
    (h : W ≤ Y.basicOpen d) : IsUnit (resG Y (h.trans (Y.basicOpen_le d)) d) := by
  have hu : IsUnit (resG Y (Y.basicOpen_le d) d) := RingedSpace.isUnit_res_basicOpen _ d
  have := hu.map (resG Y h)
  rwa [resG_resG] at this

end GlobalTheory.FlagCell.CellOpen

namespace GlobalTheory.FlagCell.CellOpen

theorem mem_finset_inf {X : Scheme.{0}} {κ : Type} [Fintype κ] (W : κ → X.Opens) (x : X)
    (h : ∀ k, x ∈ W k) : x ∈ Finset.univ.inf W := by
  rw [← SetLike.mem_coe, Opens.coe_finset_inf]
  simpa using h

theorem spans_uniR_near_image : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens) (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∀ (T : Scheme.{0}) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)), Carries π E r fl g' g w fl' → ∀ (V' : T.Opens) (hV' : V' ≤ g ⁻¹ᵁ U) (n' : (Σ a, Low (r a)) → Γ(T, V')), (∀ a, Spans (fl' a) V' (pullCol g (eU a) hV' (uniR fun s => n' ⟨a, s⟩))) → ∀ t ∈ V', ∃ (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n : (Σ a, Low (r a)) → Γ(Y, V)), g' t ∈ V ∧ ∀ a, Spans (fl a) V (pullCol π (eU a) hV (uniR fun s => n ⟨a, s⟩)) := by
  intro B Y π ι _ r E fl hE U eU heU T g' g w fl' hC V' hV' n' hn' t ht
  haveI : ∀ a, (E a).IsQuasicoherent := fun a => (hE a).isQuasicoherent
  have hy : ∀ a, ∃ W : Y.Opens, g' t ∈ W ∧ ∃ v : Fin (r a) → Γ((Scheme.Modules.pullback π).obj (E a), W),
      Spans (fl a) W v := by
    intro a
    obtain ⟨W, hW, u, -, hs⟩ := GlobalTheory.FlagZ.Loc.exists_nested_frames (fl a) (g' t) (Fin.last (r a))
    exact ⟨W, hW, fun j => ((fl a).ι (Fin.last _)).app W (u j), fun l => hs l l.is_le⟩
  choose W hyW v hv using hy
  have hπ : g' t ∈ π ⁻¹ᵁ U := by
    have h1 := hV' ht
    rw [← w] at h1
    exact h1
  let V₀ : Y.Opens := π ⁻¹ᵁ U ⊓ Finset.univ.inf W
  have hyV₀ : g' t ∈ V₀ := ⟨hπ, mem_finset_inf W _ hyW⟩
  have hV₀a : ∀ a, V₀ ≤ W a := fun a => inf_le_right.trans (Finset.inf_le (Finset.mem_univ a))
  have hV₀U : V₀ ≤ π ⁻¹ᵁ U := inf_le_left
  have hA : ∀ a, ∃ A : Matrix (Fin (r a)) (Fin (r a)) Γ(Y, V₀),
      Spans (fl a) V₀ (pullCol π (eU a) hV₀U A) := by
    intro a
    obtain ⟨A, hA⟩ := exists_pullCol π (heU a) hV₀U (fun j => resM _ (hV₀a a) (v a j))
    refine ⟨A, ?_⟩
    have := spans_res (hv a) (hV₀a a)
    convert this using 1
    funext j
    exact (hA j).symm
  choose A hA using hA
  let V'' : T.Opens := V' ⊓ g' ⁻¹ᵁ V₀
  have htV'' : t ∈ V'' := ⟨ht, hyV₀⟩
  have h₁ : V'' ≤ g' ⁻¹ᵁ V₀ := inf_le_right
  have h₂ : V'' ≤ g ⁻¹ᵁ U := inf_le_left.trans hV'
  have hmin : ∀ a (l : Fin (r a + 1)),
      IsUnit ((g'.appLE V₀ V'' h₁).hom ((A a).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det) := by
    intro a l
    have hp := GlobalTheory.T.carried_flag_triangular_frame B Y T π ι r E fl g' g w fl' hC U a (eU a) V₀ hV₀U (A a) V'' h₁ h₂ (hA a)
    have hq : Spans (fl' a) V'' (pullCol g (eU a) h₂
        (uniR fun s => resG T (inf_le_left : V'' ≤ V') (n' ⟨a, s⟩))) := by
      have := spans_res (hn' a) (inf_le_left : V'' ≤ V')
      convert this using 1
      funext j
      rw [res_pullCol, map_uniR]
    obtain ⟨M, hMt, hMd, hM⟩ := GlobalTheory.T.flag_frames_triangular_change T _ (r a) (fl' a) V'' _ _ hq hp
    have heq : (A a).map (g'.appLE V₀ V'' h₁).hom =
        (uniR fun s => resG T (inf_le_left : V'' ≤ V') (n' ⟨a, s⟩)) * M := by
      apply pullCol_injective g (heU a) h₂
      intro j
      rw [hM j, sum_smul_pullCol]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, heq,
      GlobalTheory.T.leading_minors_unipotent_mul _ (r a) _ M hMt l]
    exact isUnit_minor_of_upper M hMt hMd l
  let D : (Σ a, Fin (r a + 1)) → Y.Opens := fun p =>
    Y.basicOpen ((A p.1).submatrix (Fin.castLE p.2.is_le) (Fin.castLE p.2.is_le)).det
  let V₁ : Y.Opens := V₀ ⊓ Finset.univ.inf D
  have hyV₁ : g' t ∈ V₁ :=
    ⟨hyV₀, mem_finset_inf D _ fun p => mem_basicOpen_of_isUnit_appLE g' h₁ _ (hmin p.1 p.2) htV''⟩
  have hV₁₀ : V₁ ≤ V₀ := inf_le_left
  have hV₁U : V₁ ≤ π ⁻¹ᵁ U := hV₁₀.trans hV₀U
  have hLU : ∀ a, ∃ n : Low (r a) → Γ(Y, V₁), Spans (fl a) V₁ (pullCol π (eU a) hV₁U (uniR n)) := by
    intro a
    have hunit : ∀ l : Fin (r a + 1),
        IsUnit (((A a).map (resG Y hV₁₀)).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
      intro l
      rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      have hle : V₁ ≤ D ⟨a, l⟩ := inf_le_right.trans (Finset.inf_le (Finset.mem_univ _))
      exact isUnit_resG_of_le_basicOpen _ hle
    obtain ⟨n, M₁, hM₁t, hM₁d, hM₁⟩ := GlobalTheory.T.exists_unipotent_triangular_factor _ (r a) _ hunit
    refine ⟨n, ?_⟩
    have hs' : Spans (fl a) V₁ (pullCol π (eU a) hV₁U (uniR n * M₁)) := by
      have hs := spans_res (hA a) hV₁₀
      convert hs using 1
      funext j
      rw [res_pullCol, hM₁]
    haveI := M₁.invertibleOfIsUnitDet hM₁d
    have := GlobalTheory.T.triangular_change_spans_flag Y _ (r a) (fl a) V₁ _ M₁⁻¹ hs'
      (Matrix.blockTriangular_inv_of_blockTriangular hM₁t) (Matrix.isUnit_nonsing_inv_det _ hM₁d)
    convert this using 1
    funext j
    rw [sum_smul_pullCol, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM₁d, Matrix.mul_one]
  choose n hn using hLU
  exact ⟨V₁, hV₁U, fun p => n p.1 p.2, hyV₁, fun a => hn a⟩

end GlobalTheory.FlagCell.CellOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordinatesContDiffAtEtaleChart
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

open GlobalTheory.Points GlobalTheory.ChartGlue

theorem contDiffAt_chart_of_eqOn_ev {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {D : ℕ} (c' : AlgChart Y.str σ D)
    {g : CxPts Y.str σ → ℂ} {S : Set (CxPts Y.str σ)} (hS : IsOpen S) {W : Y.X.Opens} (a : Γ(Y.X, W))
    (hg : ∀ z ∈ S, g z = ev Y.str σ W a z) {y : CxPts Y.str σ} (hy : y ∈ c'.e.source) (hyS : y ∈ S)
    (hyW : y ∈ ptsIn Y.str σ W) : ContDiffAt ℂ 2 (g ∘ c'.e.symm) (c'.e y) := by
  have hO := isOpen_over c'.e (hS.inter (isOpen_ptsIn (p := Y.str) (σ := σ) W))
  have hm := mem_over c'.e (S := S ∩ ptsIn Y.str σ W) hy ⟨hyS, hyW⟩
  have hd : DifferentiableOn ℂ (ev Y.str σ W a ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' (S ∩ ptsIn Y.str σ W)) :=
    (c'.holo W a).mono fun v hv => ⟨hv.1, hv.2.2⟩
  have h1 : ContDiffAt ℂ 2 (ev Y.str σ W a ∘ c'.e.symm) (c'.e y) := ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ hO hd).contDiffAt (hO.mem_nhds hm)).of_le
    (by norm_cast)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hO.mem_nhds hm] with v hv
  exact hg _ hv.2.1

theorem cellMap_contDiffAt : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (x : (atlas Y σ).Pt), x.pt ∈ cellSet E E' φ f hf c A u → ContDiffAt ℂ 2 (cellMap ε f hf c u ∘ x.ch.symm) x.crd := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u n ε x hx
  obtain ⟨hcell, hsrc⟩ := hx
  have hreg := (isOpen_inCell_and_regAt F X Y ι m E E' φ f hR A u).2 _ hcell
  set c' : AlgChart Y.str σ Y.dim := x.1.1
  have hy : x.pt ∈ c'.e.source := x.2
  change ContDiffAt ℂ 2 (cellMap ε f hf c u ∘ c'.e.symm) (c'.e x.pt)
  refine contDiffAt_euclidean.2 fun a => ?_
  change ContDiffAt ℂ 2 ((fun z => cellMap ε f hf c u z a) ∘ c'.e.symm) (c'.e x.pt)
  rcases hε : ε a with b | j
  · have hS : IsOpen (ptMap σ f hf ⁻¹' c.e.source) :=
      c.e.open_source.preimage (PtsOver.continuous_map f hf _)
    refine contDiffAt_chart_of_eqOn_ev c' hS (f.app c.U (c.x b)) (fun z hz => ?_) hy hsrc ?_
    · simp only [cellMap, pt, hε, Sum.elim_inl]
      rw [c.apply_eq _ hz b, ev_app f hf]
      rfl
    · rw [mem_ptsIn]
      exact mem_ptsIn.1 (c.source_subset hsrc)
  · obtain ⟨U, hU, w, hw⟩ := (hreg j).exists_fnOf
    refine contDiffAt_chart_of_eqOn_ev c' (isOpen_ptsIn U) w (fun z hz => ?_) hy (mem_ptsIn.2 hU) (mem_ptsIn.2 hU)
    simp only [cellMap, pt, hε, Sum.elim_inr]
    rw [← hw, ratVal_fnOf hz]

end GlobalTheory.FlagCell2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentsBijectModuliComponentsStatement
section
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_components_biject_moduli_components : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag), ∃ q : s.Comp ≃ Comp s.Xo κ.c, ∀ k, Over Φ k (q k) := by
  first | exact @GlobalTheory.CovHt.Link.exists_equiv_over | exact GlobalTheory.CovHt.Link.exists_equiv_over | (intros; apply GlobalTheory.CovHt.Link.exists_equiv_over <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRefinementBundleDimEqBaseAddCardAboveDiagonaStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRefinementBundle_dim_eq_base_add_card_aboveDiagonal : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → Y.dim = X.dim + Fintype.card (Cell m) := by
  first | exact @GlobalTheory.FlagCell2.Dim.main | exact GlobalTheory.FlagCell2.Dim.main | (intros; apply GlobalTheory.FlagCell2.Dim.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChart
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isMetricFr_smoothUnitAt : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y), ∀ τ, SmoothUnitAt (atlas X σ) (fun z => H A z τ) y ∧ ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ᶠ v in 𝓝 (c.e y), MContDiffAt ∞ (fun u => H A (c.e.symm u) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
  intro F _ σ X ι _ m k E H hH y A hA τ
  set U : Set (CxPts X.str σ) := interior {z : CxPts X.str σ | A ∈ E.S (under z)} with hU
  have hyU : y ∈ U := mem_interior_iff_mem_nhds.2 (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E y A hA)
  have hUo : IsOpen U := isOpen_interior
  have hUS : ∀ z ∈ U, A ∈ E.S (under z) := fun z hz => interior_subset (s := {z : CxPts X.str σ | A ∈ E.S (under z)}) hz
  have key : ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ᶠ v in 𝓝 (c.e y),
      MContDiffAt ∞ (fun u => H A (c.e.symm u) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
    intro c hc
    have ho : IsOpen (c.e.target ∩ c.e.symm ⁻¹' U) := c.e.isOpen_inter_preimage_symm hUo
    have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' U :=
      ⟨c.e.map_source hc, by simpa [Set.mem_preimage, c.e.left_inv hc] using hyU⟩
    filter_upwards [ho.mem_nhds hm] with v hv
    refine ⟨fun i j => ?_, hH.posDef _ A (hUS _ hv.2) τ⟩
    have hre := contDiffOn_chart (S := U) (f := fun z => (H A z τ i j).re)
      (fun z hz => (hH.smooth z A (hUS z hz) τ i j).1) c
    have him := contDiffOn_chart (S := U) (f := fun z => (H A z τ i j).im)
      (fun z hz => (hH.smooth z A (hUS z hz) τ i j).2) c
    have h1 := (hre.contDiffAt (ho.mem_nhds hv))
    have h2 := (him.contDiffAt (ho.mem_nhds hv))
    have h3 : ContDiffAt ℝ ∞ (fun u => ((((H A (c.e.symm u) τ i j).re : ℝ) : ℂ) +
        (((H A (c.e.symm u) τ i j).im : ℝ) : ℂ) * Complex.I)) v :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp v h1).add
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp v h2).mul contDiffAt_const)
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    simp [Complex.re_add_im]
  refine ⟨⟨?_, fun c hc => (key c hc).mono fun v hv => hv.1⟩, key⟩
  exact (Matrix.isUnit_iff_isUnit_det _).1 (hH.posDef y A hA τ).isUnit

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsConnectedIrreducibleBaseStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.FlagConnect
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flags_connected_irreducible_base : ∀ (L : Type) [Field L] (B : Scheme.{0}) (s : Spec (CommRingCat.of L) ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (G₁ G₂ : ∀ a, Vert.Flag ((Scheme.Modules.pullback s).obj (E a)) (r a)), ∃ (T : Scheme.{0}) (g : T ⟶ B) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (G : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)) (v₁ : t₁ ≫ g = s) (v₂ : t₂ ≫ g = s), IrreducibleSpace T ∧ Carries g E r G t₁ s v₁ G₁ ∧ Carries g E r G t₂ s v₂ G₂ := by
  first | exact @GlobalTheory.FlagPath.exists_irreducible_family | exact GlobalTheory.FlagPath.exists_irreducible_family | (intros; apply GlobalTheory.FlagPath.exists_irreducible_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerIsoFlagTangentStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_iso_flag_tangent : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y := by
  first | exact @GlobalTheory.FlagTan.ksIso_psiSet | exact GlobalTheory.FlagTan.ksIso_psiSet | (intros; apply GlobalTheory.FlagTan.ksIso_psiSet <;> assumption)
end

