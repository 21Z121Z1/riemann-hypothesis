import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0110
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0128
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualCompSelfAdjointStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_sqrt_smul_comp_of_invariant : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ) (T : V ≃ₜ V) (δ : ℝ≥0), δ ≠ 0 → μ = δ • μ.map T → (∀ x y, χ x (T y) = χ (T x) y) → SelfDual μ χ → SelfDual (NNReal.sqrt δ • μ) (fun x y => χ x (T y)) := by
  first | exact @GlobalTheory.GaugeEx.selfDual_comp_selfAdjoint | exact GlobalTheory.GaugeEx.selfDual_comp_selfAdjoint | (intros; apply GlobalTheory.GaugeEx.selfDual_comp_selfAdjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepDatumBoundedAtTypePrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.BddG

open GlobalTheory.LastSteps GlobalTheory.ColPeriod

theorem homBdd_of_good {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
    {n' c' n c m : ℕ} (hc' : c' ≤ m) (hc : c + 1 ≤ m) {Φ : HomE E (n' + c') (n + c) → K}
    (h : Good P (homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) Φ) :
    HomBdd P m Φ := by
  have hq : (qOf P : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  refine ⟨fun x hx => (intHom_iff _).2 fun s l => ?_, fun x y hy => ?_⟩
  · have h1 := mem_homS_sclLat.1 (h.1 x hx) l s
    have hs := s.2
    have e : 0 ≤ (m : ℤ) - (LocE.scE n' (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1) := by
      unfold LocE.scE
      dsimp only
      split_ifs <;> omega
    convert h1.mul (intAt_zpow e) using 1
    rw [mul_assoc, ← zpow_add₀ hq, add_sub_cancel, zpow_natCast, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  · have h1 : ((qOf P : E) ^ ((m : ℤ) - 1)) • y ∈
        homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1) := by
      refine mem_homS_sclLat.2 fun l s => ?_
      have hl := l.2
      have e : 0 ≤ (m : ℤ) - 1 + (LocE.scE n' (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1) := by
        unfold LocE.scE
        dsimp only
        split_ifs <;> omega
      convert ((intHom_iff _).1 hy s l).mul (intAt_zpow e) using 1
      rw [zpow_add₀ hq, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h2 := h.2.1 x _ h1
    rwa [smul_smul, zpow_sub_one₀ hq, mul_comm _ (qOf P : E)⁻¹, mul_inv_cancel_left₀ hq, zpow_natCast] at h2

theorem good_omPhi_two {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hi : i + 2 ≤ R.m) (hP : P.1 ∈ Pr.vGs)
    {hal : AutY X R i} {h : AutY X R (i + 1)} (ha : hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1))
    (hb : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1)) :
    Good P.1 (homS (LocE.lamY P.1 (qOf P.1) (R.N i) (cOf R i) fun i => i + 1)
      (LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) fun i => i + 1)) (omPhi Ch sel mu cst i P hal h) := by
  have h1 : R.k ≤ R.N i := Nat.le_add_right _ _
  have h2 : R.k ≤ R.N (i + 1) := Nat.le_add_right _ _
  have h3 : R.r + (i + 1 - 1) * R.t = R.N i + cOf R i := by
    unfold Ranks.r Ranks.N cOf
    rw [Nat.add_sub_cancel, mul_add i]
    omega
  have h4 : R.N i + cOf R i ≤ R.N (i + 1) + cOf R (i + 1) := by
    unfold Ranks.N cOf
    rw [add_mul i]
    omega
  unfold lamYat at ha hb
  rw [if_pos hP] at ha hb
  refine good_om_two ?_ _ _ _ ha hb
  unfold PhiAt
  rw [if_pos hP]
  split_ifs
  · exact good_PhiGS _ _ h1 h2 h3 h4
  · exact good_PhiG _ _ h1 h2 h3 h4

theorem omPhi_bdd_type {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hi : i + 2 ≤ R.m) (hP : P.1 ∈ Pr.vGs)
    (hal : AutY X R i) (h : AutY X R (i + 1)) (ha : hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1))
    (hb : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1)) :
    HomBdd P.1 R.m (omPhi Ch sel mu cst i P hal h) ∧
      ∀ x, omPhi Ch sel mu cst i P hal h x ≠ 0 → IntAt P.1 ((qOf P.1 : X.E) * Loc.chArg x) := by
  have hg := good_omPhi_two Ch sel mu cst i P hi hP ha hb
  refine ⟨homBdd_of_good (by unfold cOf; omega) (by unfold cOf; omega) hg, fun x hx => ?_⟩
  have := GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (chArg_int (hg.1 x hx))
  rwa [mul_neg, neg_neg] at this

end GlobalTheory.Mem.Col2.BddG

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TailProdMulOfLatticeMassMulStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tailProd_mul_of_lattice_mass_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n₁ M₁ n₂ M₂ n₃ M₃ : ℕ) (mi : Measure (Fin n₁ → Fin M₁ → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₁ → Fin M₁ → Fv F v ⊗[F] E)) (mi' : Measure (Fin n₂ → Fin M₂ → Ainf F ⊗[F] E)) (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₂ → Fin M₂ → Fv F v ⊗[F] E)) (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₃ → Fin M₃ → Fv F v ⊗[F] E)) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → Conv b mi' mv' → (∀ v ∉ S₀, Nv v (latV b v) = mv v (latV b v) * mv' v (latV b v)) → (Summable fun v => |(Nv v (latV b v)).toReal - 1|) ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S → tailProd b Nv S = tailProd b mv S * tailProd b mv' S := by
  first | exact @GlobalTheory.GaugeEx.tailProd_mul_of_mass_mul | exact GlobalTheory.GaugeEx.tailProd_mul_of_mass_mul | (intros; apply GlobalTheory.GaugeEx.tailProd_mul_of_mass_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorNiceRingArtinianReducedOpenUnitsStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_niceRing_artinian_reduced_openUnits : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsOpenUnits (R ⊗[F] E) := by
  first | exact @GlobalTheory.GaugeEx.nice_tensor | exact GlobalTheory.GaugeEx.nice_tensor | (intros; apply GlobalTheory.GaugeEx.nice_tensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMapReferenceTupleGoodPartOntoRows
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem kOf_apply_self_on {K : Type} [Field K] (σ : K →+* ℂ) (a : K) : kOf σ (σ a) = a := by
  unfold kOf
  have h : ∃ b : K, σ b = σ a := ⟨a, rfl⟩
  rw [dif_pos h]
  exact σ.injective h.choose_spec

theorem relMat_self_on {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] E)
    (hf : Function.Injective f) : relMat f f = 1 := by
  ext i k
  have h : ∃ y, f y = f (Pi.single k 1) := ⟨_, rfl⟩
  have : solve f (f (Pi.single k 1)) = Pi.single k 1 := by
    unfold solve
    rw [dif_pos h]
    exact hf h.choose_spec
  simp only [relMat, Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]

theorem kMat_one_on {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} : kMat σ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i k
  simp only [kMat, Matrix.map_apply, Matrix.one_apply]
  split_ifs
  · simpa using kOf_apply_self_on σ 1
  · simpa using kOf_apply_self_on σ 0

theorem thetaMap_referenceTuple_goodPart_onto_rows : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.IotaRd cr → R.ReadingFormsSpanGoodSubspace → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D Bs A X fc s R cr eV hF hI hV
  have h1 : X.rowMat cr true Bs.μ0 = 1 := by
    unfold CxData.rowMat CxData.rowMatC
    rw [relMat_self_on _ hF.h2.1, kMat_one_on]
  rw [eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨x, hx⟩ := R.eRR.surjective (D.div.RR.b i)
  obtain ⟨y, hy⟩ := hF.wf.Pq_surj Bs.μ0 x
  refine ⟨R.jV y, ?_, ?_⟩
  · have : R.jV y ∈ Submodule.span ℂ (Set.range R.jV) := Submodule.subset_span ⟨y, rfl⟩
    rw [hV] at this
    exact this
  · have := hI y
    rw [h1, Matrix.one_mulVec] at this
    exact this.trans (congrArg D.jEE ((congrArg R.eRR hy).trans hx))

end GlobalTheory.Mem.SJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeAndTwistPlacesOverOtherThanSplitStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2 Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeAndTwistPlaces_over_other_than_split : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (t : T) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.v ∉ gPl D → s.w ∈ L.Q t → (∀ PP ∈ L.Pg, ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) ∧ (∀ PP ∈ L.Q t, PP ≠ s.w → ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) := by
  first | exact @GlobalTheory.OtherPlaces.over_ne | exact GlobalTheory.OtherPlaces.over_ne | (intros; apply GlobalTheory.OtherPlaces.over_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupPointsEquivOfChangeOfBasisStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) → (∃! e : HA R σ J ≃* HA R σ J', ∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ ∀ e : HA R σ J ≃* HA R σ J', (∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) → Continuous e ∧ Continuous e.symm := by
  first | exact @GlobalTheory.GaugeFrameBasis.frame_basis | exact GlobalTheory.GaugeFrameBasis.frame_basis | (intros; apply GlobalTheory.GaugeFrameBasis.frame_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupRealPointsEquivPiIndefiniteUnitary
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.InfGroup

section General

variable {S : Type} [CommRing S] {I : Type} {M : ℕ}

def lift (e : S ≃+* (I → ℂ)) (m : I → Matrix (Fin M) (Fin M) ℂ) : Matrix (Fin M) (Fin M) S :=
  Matrix.of fun a b => e.symm fun i => m i a b

variable {e : S ≃+* (I → ℂ)} {θ : I → (S →+* ℂ)}

theorem lift_map (he : ∀ x i, e x i = θ i x) (m : I → Matrix (Fin M) (Fin M) ℂ) (i : I) :
    (lift e m).map (θ i) = m i := by
  ext a b
  simp [lift, ← he]

theorem ext_map (he : ∀ x i, e x i = θ i x) {X Y : Matrix (Fin M) (Fin M) S}
    (h : ∀ i, X.map (θ i) = Y.map (θ i)) : X = Y := by
  ext a b
  apply e.injective
  funext i
  rw [he, he]
  exact congrFun (congrFun (h i) a) b

theorem cT_map {s : S →+* S} {t : S →+* ℂ} (hs : ∀ x, t (s x) = star (t x))
    (X : Matrix (Fin M) (Fin M) S) : (Formalism.UG.cT s X).map t = (X.map t)ᴴ := by
  ext a b
  simp [Formalism.UG.cT, hs]

theorem conj_mul {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) (X Y : Matrix n n ℂ) :
    A * X * B * (A * Y * B) = A * (X * Y) * B := by
  calc A * X * B * (A * Y * B) = A * X * (B * A) * Y * B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hBA]; simp only [Matrix.mul_assoc, Matrix.mul_one]

theorem conj_conj {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) (X : Matrix n n ℂ) :
    B * (A * X * B) * A = X := by
  calc B * (A * X * B) * A = (B * A) * X * (B * A) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hBA]; simp

theorem conj_unitary {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) {G X : Matrix n n ℂ} {K : Matrix m m ℂ}
    (hK : Bᴴ * G * B = K) (hX : Xᴴ * G * X = G) :
    (A * X * B)ᴴ * K * (A * X * B) = K := by
  rw [← hK]
  calc (A * X * B)ᴴ * (Bᴴ * G * B) * (A * X * B)
      = Bᴴ * (Xᴴ * ((B * A)ᴴ * G * (B * A)) * X) * B := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hBA, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]

theorem exists_equiv [TopologicalSpace S] (he : ∀ x i, e x i = θ i x) (hc : Continuous e)
    (hc' : Continuous e.symm) (s : S →+* S) (hs : ∀ x i, θ i (s x) = star (θ i x))
    (J : Matrix (Fin M) (Fin M) S) (P Q : I → ℕ)
    (A : ∀ i, Matrix (Fin (P i) ⊕ Fin (Q i)) (Fin M) ℂ)
    (B : ∀ i, Matrix (Fin M) (Fin (P i) ⊕ Fin (Q i)) ℂ)
    (hAB : ∀ i, A i * B i = 1) (hBA : ∀ i, B i * A i = 1)
    (hA : ∀ i, (A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i = J.map (θ i)) :
    ∃ f : Formalism.UG.UJ s J ≃ₜ* (∀ i, UpqT (P i) (Q i)), ∀ h i, UpqT.mat (f h i) * A i =
      A i * ((h.1 : GL (Fin M) S) : Matrix (Fin M) (Fin M) S).map (θ i) := by
  have hB : ∀ i, (B i)ᴴ * J.map (θ i) * B i = Formalism.UG.Jpq (P i) (Q i) := by
    intro i
    rw [← hA]
    calc (B i)ᴴ * ((A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i) * B i
        = (A i * B i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * (A i * B i) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hAB]; simp
  have hone : ∀ i, (1 : Matrix (Fin M) (Fin M) S).map (θ i) = 1 := fun i =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have hθ : ∀ i, Continuous (θ i) := fun i => by
    have : (θ i : S → ℂ) = fun x => e x i := funext fun x => (he x i).symm
    rw [this]
    exact (continuous_apply i).comp hc
  have hfw : ∀ (h : Formalism.UG.UJ s J) (i : I), ∃ g : UpqT (P i) (Q i),
      UpqT.mat g = A i * h.1.1.map (θ i) * B i := by
    intro h i
    have hh : Formalism.UG.cT s h.1.1 * J * h.1.1 = J := h.2
    have h2 := congrArg (fun X => Matrix.map X (θ i)) hh
    simp only [Matrix.map_mul, cT_map (fun x => hs x i)] at h2
    have : A i * h.1.1.map (θ i) * B i ∈ Set.range (UpqT.mat (P := P i) (Q := Q i)) := by
      rw [GlobalTheory.UpqTopology.range_mat]
      exact conj_unitary (hBA i) (hB i) h2
    exact this
  choose fw hfw using hfw
  have hmul : ∀ {p q : ℕ} (a b : UpqT p q), UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b :=
    fun _ _ => rfl
  have hm1 : ∀ {p q : ℕ}, UpqT.mat (1 : UpqT p q) = 1 := rfl
  have hinj : ∀ (p q : ℕ), Function.Injective (UpqT.mat (P := p) (Q := q)) :=
    fun _ _ => GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective
  let L : (∀ i, UpqT (P i) (Q i)) → Matrix (Fin M) (Fin M) S :=
    fun g => lift e fun i => B i * UpqT.mat (g i) * A i
  have hL : ∀ g i, (L g).map (θ i) = B i * UpqT.mat (g i) * A i := fun g i => lift_map he _ i
  have hLmul : ∀ g g', L g * L g' = L (g * g') := by
    intro g g'
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, hL, hL, hL, conj_mul (hAB i), Pi.mul_apply, hmul]
  have hL1 : L 1 = 1 := by
    refine ext_map he fun i => ?_
    rw [hL, Pi.one_apply, hm1, Matrix.mul_one, hBA, hone]
  have hLu : ∀ g, Formalism.UG.cT s (L g) * J * L g = J := by
    intro g
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, Matrix.map_mul, cT_map (fun x => hs x i), hL]
    exact conj_unitary (hAB i) (hA i) (GlobalTheory.UpqTopology.mat_unitary (g i))
  have hLc : Continuous L := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    refine hc'.comp (continuous_pi fun i => ?_)
    have : Continuous fun g : ∀ i, UpqT (P i) (Q i) => B i * UpqT.mat (g i) * A i :=
      (continuous_const.matrix_mul
        (GlobalTheory.UpqTopology.continuous_mat.comp (continuous_apply i))).matrix_mul continuous_const
    exact this.matrix_elem a b
  let bw : (∀ i, UpqT (P i) (Q i)) → Formalism.UG.UJ s J := fun g =>
    ⟨⟨L g, L g⁻¹, by rw [hLmul, mul_inv_cancel, hL1], by rw [hLmul, inv_mul_cancel, hL1]⟩, hLu g⟩
  haveI : ∀ i, IsTopologicalGroup (UpqT (P i) (Q i)) := fun i => (GlobalTheory.UpqTopology.upq_lcsc _ _).1
  refine ⟨
    { toFun := fw
      invFun := bw
      left_inv := fun h => ?_
      right_inv := fun g => ?_
      map_mul' := fun h h' => ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun h i => ?_⟩
  · refine Subtype.ext (Units.ext (ext_map he fun i => ?_))
    change (L (fw h)).map (θ i) = _
    rw [hL, hfw, conj_conj (hBA i)]
  · funext i
    apply hinj
    rw [hfw]
    change A i * (L g).map (θ i) * B i = _
    rw [hL, conj_conj (hAB i)]
  · funext i
    apply hinj
    rw [Pi.mul_apply, hmul, hfw, hfw, hfw, conj_mul (hBA i), ← Matrix.map_mul]
    rfl
  · refine continuous_pi fun i => GlobalTheory.UpqTopology.isInducing_mat.continuous_iff.2 ?_
    have : (UpqT.mat ∘ fun h => fw h i) = fun h : Formalism.UG.UJ s J => A i * h.1.1.map (θ i) * B i :=
      funext fun h => hfw h i
    rw [this]
    exact (continuous_const.matrix_mul ((Units.continuous_val.comp continuous_subtype_val).matrix_map
      (hθ i))).matrix_mul continuous_const
  · refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hLc, hLc.comp continuous_inv⟩) _
  · change UpqT.mat (fw h i) * A i = _
    rw [hfw, Matrix.mul_assoc, hBA, Matrix.mul_one]

end General

theorem real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)) (P Q : I → ℕ) (A : ∀ i, Matrix (Fin (P i) ⊕ Fin (Q i)) (Fin M) ℂ), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → (∀ i, Formalism.UG.HasSignature (J.map (τ i)) (P i) (Q i)) → (∀ i, (A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i = J.map (τ i)) → ∃ e : HA (Ainf F) σ J ≃ₜ* (∀ i, UpqT (P i) (Q i)), ∀ h i, UpqT.mat (e h i) * A i = A i * ((HA.mat (Ainf F) σ J h : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).map (θ i) := by
  intro F E _ _ _ _ _ σ M J I _ τ θ P Q A hcm hfam hθ hsig hA
  obtain ⟨e, he, hc, hc', hs⟩ := GlobalTheory.T.exists_archAdeleTensor_equiv_complex_cmType F E σ I τ θ hcm hfam hθ
  choose B hAB hBA using fun i =>
    (GlobalTheory.Mem.SignatureFactor.exists_factor M (P i) (Q i) _ (hsig i)).2.2 (A i) (hA i)
  refine exists_equiv he hc hc' (sigR (Ainf F) σ) (fun x i => by rw [← he, ← he, hs])
    (JR (Ainf F) J) P Q A B hAB hBA fun i => ?_
  rw [hA]
  ext a b
  exact ((hθ i).1 (J a b)).symm

end GlobalTheory.Mem.InfGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemenStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → (consCol x B).det ≠ 0 ∧ (∃! e : Hstab R σ J x ≃* HA R σ J', ∀ g : Hstab R σ J x, FrameRelR R σ J J' B (g : HA R σ J) (e g)) ∧ ∀ e : Hstab R σ J x ≃* HA R σ J', (∀ g : Hstab R σ J x, FrameRelR R σ J J' B (g : HA R σ J) (e g)) → Continuous e ∧ Continuous e.symm := by
  first | exact @GlobalTheory.FrameStep.frameStep | exact GlobalTheory.FrameStep.frameStep | (intros; apply GlobalTheory.FrameStep.frameStep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardHeckeOperatorCommuteDiamond
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.UpDia

section Local
variable {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]

theorem inc_dil {res : R →+* k} (hs : Function.Surjective res) {t : R} {p q : Pr R V k} (hp : p.Ok res)
    (h : Pr.Inc res t p q) {a : k} (ha : a ≠ 0) : Pr.Inc res t (p.dil a) (q.dil a) := by
  obtain ⟨h1, h2, e, h3, h4⟩ := h
  obtain ⟨b, hb⟩ := hs a⁻¹
  have he : e ∈ q.L := by
    by_contra hn
    rw [h1.off _ hn] at h3
    exact zero_ne_one h3
  have hte : t • e ∈ p.L := by
    by_contra hn
    rw [hp.off _ hn] at h4
    exact zero_ne_one h4
  refine ⟨h1.dil ha, fun y => ?_, b • e, ?_, ?_⟩
  · show y ∈ p.L ↔ y ∈ q.L ∧ a * q.f y = 0
    rw [h2 y, mul_eq_zero, or_iff_right ha]
  · show a * q.f _ = 1
    rw [h1.smul _ _ he, h3, hb, mul_one, mul_inv_cancel₀ ha]
  · show a * p.f _ = 1
    rw [smul_comm, hp.smul _ _ hte, h4, hb, mul_one, mul_inv_cancel₀ ha]

theorem inc_dil_iff {res : R →+* k} (hs : Function.Surjective res) {t : R} {p : Pr R V k} (hp : p.Ok res)
    (q : Pr R V k) {a : k} (ha : a ≠ 0) : Pr.Inc res t (p.dil a) (q.dil a) ↔ Pr.Inc res t p q := by
  refine ⟨fun h => ?_, fun h => inc_dil hs hp h ha⟩
  have := inc_dil hs (hp.dil ha) h (inv_ne_zero ha)
  rwa [Pr.dil_dil, Pr.dil_dil, inv_mul_cancel₀ ha, Pr.dil_one, Pr.dil_one] at this

def dilEquiv {a : k} (ha : a ≠ 0) : Pr R V k ≃ Pr R V k where
  toFun q := q.dil a
  invFun q := q.dil a⁻¹
  left_inv q := by
    show (q.dil a).dil a⁻¹ = q
    rw [Pr.dil_dil, inv_mul_cancel₀ ha, Pr.dil_one]
  right_inv q := by
    show (q.dil a⁻¹).dil a = q
    rw [Pr.dil_dil, mul_inv_cancel₀ ha, Pr.dil_one]

end Local

theorem atV_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)} {η : GA σ J}
    (h : AtV v η) (δ : GA σ J) : AtV v (δ⁻¹ * η * δ) := by
  intro v' hv'
  have h1 := h v' hv'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h1, mul_one, inv_mul_cancel]

theorem upAd_dia : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E), Function.Surjective res → (∀ x, (p x).Ok res) → ∀ g ∈ AdFun S emb, ∀ (v' : HeightOneSpectrum (𝓞 F)) (hv' : (T : 𝓞 F) ∈ v'.asIdeal) (a : ℤ) (δ : GA σ J), v' ∉ bad → (v' = v → (a : k) ≠ 0) → IsDia S v' hv' a δ → ∀ x, upAd res t v p (fun y => g (y * δ)) x = upAd res t v p g (x * δ) := by
  intro F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hP res t hs hok g hg v' hv' a δ hb' ha hδ x
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.adelicForm_values_near_point_spec F E σ n J T f bad ι S emb v hv k p hb hP g hg
  by_cases hvv : v' = v
  · subst hvv
    have ha' := ha rfl
    unfold upAd
    rw [hP.2.2 x δ a hδ, h2 x δ hδ.1]
    refine finsum_mem_eq_of_bijOn (fun q => q.dil (a : k)) ?_ (fun q _ => (h3 a δ x q ha' hδ).symm)
    refine (dilEquiv ha').bijOn' ?_ ?_
    · intro q hq
      exact inc_dil hs (hok x) hq ha'
    · intro q hq
      have := inc_dil hs ((hok x).dil ha') hq (inv_ne_zero ha')
      rw [Pr.dil_dil, inv_mul_cancel₀ ha', Pr.dil_one] at this
      exact this
  · have hp : ∀ y, p (y * δ) = p y := fun y => (hP.2.1 y δ).2 (by
      rw [hδ.1 v (Ne.symm hvv)]; exact one_mem _)
    have key : valAt v p (fun y => g (y * δ)) x = valAt v p g (x * δ) := by
      funext q
      by_cases h : ∃ η, AtV v η ∧ p (x * η) = q
      · have hc := h.choose_spec
        have e : x * δ * (δ⁻¹ * h.choose * δ) = x * h.choose * δ := by group
        have := h1 (x * δ) _ (atV_conj hc.1 δ)
        rw [e, hp, hc.2] at this
        rw [this]
        unfold valAt
        rw [dif_pos h]
      · have h' : ¬ ∃ η, AtV v η ∧ p (x * δ * η) = q := by
          rintro ⟨η, hη, hq⟩
          refine h ⟨δ⁻¹⁻¹ * η * δ⁻¹, atV_conj hη _, ?_⟩
          rw [← hp, ← hq]
          congr 1
          group
        unfold valAt
        rw [dif_neg h, dif_neg h']
    unfold upAd
    rw [hp, key]

end GlobalTheory.LevelHecke.UpDia
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedActionStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vectorTupleProductMeasure_two_sided_action : ∀ (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S], IsArtinianRing S → IsReduced S → ∀ (lam : Measure S), lam.IsAddHaarMeasure → ∀ (n M : ℕ) (g : Matrix (Fin M) (Fin M) S) (γ : Matrix (Fin n) (Fin n) S), IsUnit g.det → IsUnit γ.det → tupMeas lam n M = (modu S g.det ^ n * modu S γ.det ^ M) • (tupMeas lam n M).map (lrAct g γ) := by
  first | exact @GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct | exact GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct | (intros; apply GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct <;> assumption)
end

