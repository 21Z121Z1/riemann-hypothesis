import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0720
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0711
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0712
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0710
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0708
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0718
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0713
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0716
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitalSignAlmostEverywhere
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiltration
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibOrd.ChainFilt

section generic
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

def subMap (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v)) (S : Subrepresentation ρ) :
    Subrepresentation σ :=
  ⟨S.toSubmodule.map f, by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, S.apply_mem_toSubmodule g hv, hf g v⟩⟩

theorem subMap_mono (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v))
    {S T : Subrepresentation ρ} (h : S ≤ T) : subMap f hf S ≤ subMap f hf T := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

theorem subMap_bot (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v)) :
    subMap f hf (⊥ : Subrepresentation ρ) = ⊥ :=
  Subrepresentation.toSubmodule_injective (Submodule.map_bot f)

theorem subQuot_subMap_equiv (f : V →ₗ[ℂ] W) (hf : ∀ x v, f (ρ x v) = σ x (f v))
    (hi : Function.Injective f) (S T : Subrepresentation ρ) :
    Nonempty ((subQuot S T).Equiv (subQuot (subMap f hf S) (subMap f hf T))) := by
  let e : S.toSubmodule ≃ₗ[ℂ] (subMap f hf S).toSubmodule :=
    Submodule.equivMapOfInjective f hi S.toSubmodule
  have he : (T.toSubmodule.comap S.toSubmodule.subtype).map e.toLinearMap =
      (subMap f hf T).toSubmodule.comap (subMap f hf S).toSubmodule.subtype := by
    ext ⟨w, hw⟩
    constructor
    · rintro ⟨⟨v, hvS⟩, hvT, hv⟩
      have hv' : f v = w := congrArg Subtype.val hv
      exact ⟨v, hvT, hv'⟩
    · rintro ⟨v, hvT, hv⟩
      obtain ⟨u, hu, rfl⟩ := hw
      have huv : v = u := hi hv
      subst huv
      exact ⟨⟨v, hu⟩, hvT, Subtype.ext rfl⟩
  let q := Submodule.Quotient.equiv _ _ e he
  refine ⟨Representation.Equiv.mk q fun g => ?_⟩
  refine Submodule.linearMap_qext _ ?_
  ext v
  show Submodule.Quotient.mk (e ⟨ρ g v.1, S.apply_mem_toSubmodule g v.2⟩) =
    Submodule.Quotient.mk (⟨σ g (f v.1), (subMap f hf S).apply_mem_toSubmodule g ⟨v.1, v.2, rfl⟩⟩ : _)
  congr 1
  exact Subtype.ext (hf g v.1)

end generic

section chain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {R : ℕ → GRep k n → Prop} {Z : ℕ → Prop}

theorem chain_le {a b : ℕ} {X : GRep k n} (h : Chain R Z a b X) : a ≤ b := by
  induction h <;> omega

theorem filt_extend {a b : ℕ} {X Y : GRep k n} (f : Y.V →ₗ[ℂ] X.V)
    (hf : ∀ x v, f (Y.ρ x v) = X.ρ x (f v)) (hi : Function.Injective f) (hab : a < b)
    (F' : ℕ → Subrepresentation Y.ρ) (hanti : Antitone F') (htop : F' (a + 1) = ⊤) (hbot : F' b = ⊥)
    (hst : ∀ i, a + 1 ≤ i → i < b →
      (∃ A, R i A ∧ Nonempty ((subQuot (F' i) (F' (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F' i = F' (i + 1)))
    (h0 : (∃ A, R a A ∧ Nonempty ((subQuot ⊤ (subMap f hf ⊤)).Equiv A.ρ)) ∨
      (Z a ∧ (⊤ : Subrepresentation X.ρ) = subMap f hf ⊤)) :
    ∃ F : ℕ → Subrepresentation X.ρ, Antitone F ∧ F a = ⊤ ∧ F b = ⊥ ∧ ∀ i, a ≤ i → i < b →
      (∃ A, R i A ∧ Nonempty ((subQuot (F i) (F (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F i = F (i + 1)) := by
  classical
  obtain ⟨F, hF1, hF2⟩ : ∃ F : ℕ → Subrepresentation X.ρ, (∀ i, i ≤ a → F i = ⊤) ∧
      (∀ i, a < i → F i = subMap f hf (F' i)) :=
    ⟨fun i => if i ≤ a then ⊤ else subMap f hf (F' i), fun i h => if_pos h,
      fun i h => if_neg (by omega)⟩
  refine ⟨F, ?_, hF1 a le_rfl, ?_, ?_⟩
  · intro i j hij
    by_cases h2 : i ≤ a
    · rw [hF1 i h2]; exact le_top
    · rw [hF2 i (by omega), hF2 j (by omega)]; exact subMap_mono f hf (hanti hij)
  · rw [hF2 b hab, hbot, subMap_bot]
  · intro i hai hib
    rcases hai.eq_or_lt with rfl | hlt
    · rw [hF1 a le_rfl, hF2 (a + 1) (by omega), htop]
      exact h0
    · rw [hF2 i hlt, hF2 (i + 1) (by omega)]
      rcases hst i hlt hib with ⟨A, hR, ⟨e⟩⟩ | ⟨hZ, he⟩
      · obtain ⟨e'⟩ := subQuot_subMap_equiv f hf hi (F' i) (F' (i + 1))
        exact Or.inl ⟨A, hR, ⟨e'.symm.trans e⟩⟩
      · exact Or.inr ⟨hZ, by rw [he]⟩

theorem exists_filtration : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (R : ℕ → GRep k n → Prop) (Z : ℕ → Prop) (a b : ℕ)
    (X : GRep k n), Chain R Z a b X → ∃ F : ℕ → Subrepresentation X.ρ, Antitone F ∧ F a = ⊤ ∧
      F b = ⊥ ∧ ∀ i, a ≤ i → i < b →
        (∃ A, R i A ∧ Nonempty ((subQuot (F i) (F (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F i = F (i + 1)) := by
  intro k _ _ _ _ n R Z a b X h
  induction h with
  | nil a X hs =>
    refine ⟨fun _ => ⊥, fun _ _ _ => le_rfl, ?_, rfl, fun i h1 h2 => by omega⟩
    refine Subrepresentation.toSubmodule_injective ?_
    ext v
    have : v = 0 := Subsingleton.elim _ _
    subst this
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  | @step a b X Y A hR hs hc ih =>
    obtain ⟨f, g, hf, hg, hi, hsur, he⟩ := hs
    obtain ⟨F', h1, h2, h3, h4⟩ := ih
    have hab := chain_le hc
    refine filt_extend f hf hi (by omega) F' h1 h2 h3 h4 (Or.inl ⟨A, hR, ?_⟩)
    obtain ⟨S, hS, e⟩ := GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv X.ρ A.ρ
      ⟨g, fun x => LinearMap.ext (hg x)⟩ hsur
    have hS' : S = subMap f hf ⊤ := by
      refine Subrepresentation.toSubmodule_injective ?_
      refine hS.trans ?_
      show LinearMap.ker g = Submodule.map f ⊤
      rw [Submodule.map_top, he]
    exact hS' ▸ e
  | @skip a b X Y hZ he hc ih =>
    obtain ⟨e⟩ := he
    obtain ⟨F', h1, h2, h3, h4⟩ := ih
    have hab := chain_le hc
    refine filt_extend e.toLinearEquiv.toLinearMap (eint e) e.toLinearEquiv.injective (by omega)
      F' h1 h2 h3 h4 (Or.inr ⟨hZ, ?_⟩)
    refine Subrepresentation.toSubmodule_injective ?_
    show ⊤ = Submodule.map e.toLinearEquiv.toLinearMap ⊤
    rw [Submodule.map_top, LinearEquiv.range]

end chain

end GlobalTheory.CompanionTheory.LeibOrd.ChainFilt

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenMulEqIdem
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.UnitNbhd

open PositivityTheory.RgEis (eSF)

section Gen

variable {R A : Type*} [CommRing R] [Nontrivial R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]

theorem exists_mul_eq_norm (a : A) : ∃ c, a * c = algebraMap R A (Algebra.norm R a) := by
  classical
  let b := Module.Free.chooseBasis R A
  let M := Algebra.leftMulMatrix b a
  refine ⟨Matrix.toLin b b M.adjugate 1, ?_⟩
  have h1 : Algebra.norm R a = M.det := Algebra.norm_eq_matrix_det b a
  have h2 : Matrix.toLin b b M = LinearMap.mulLeft R a := by
    simp only [M, Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix]
    rfl
  have h3 : Matrix.toLin b b M (Matrix.toLin b b M.adjugate 1) = Matrix.toLin b b (M * M.adjugate) 1 := by
    rw [Matrix.toLin_mul b b b]; rfl
  have h4 : a * Matrix.toLin b b M.adjugate 1 = Matrix.toLin b b M (Matrix.toLin b b M.adjugate 1) := by
    rw [h2]; rfl
  rw [h4, h3, Matrix.mul_adjugate, h1, map_smul, Matrix.toLin_one, LinearMap.smul_apply, LinearMap.id_apply, Algebra.algebraMap_eq_smul_one]

theorem continuous_norm [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace A] [IsModuleTopology R A] :
    Continuous (fun a : A => Algebra.norm R a) := by
  classical
  let b := Module.Free.chooseBasis R A
  have h : (fun a : A => Algebra.norm R a) = fun a => (Algebra.leftMulMatrix b a).det := by
    funext a; exact Algebra.norm_eq_matrix_det b a
  rw [h]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  have : (fun a : A => Algebra.leftMulMatrix b a i j) = (b.coord i) ∘ₗ (LinearMap.mulRight R (b j)) := by
    funext a
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

end Gen

theorem exists_mul_eq_eSF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : AF F)
    (h1 : ∀ w, evInf F w n ≠ 0) (h2 : ∀ v ∈ S, evFin F v n ≠ 0) : ∃ m : AF F, n * m = eSF S := by
  classical
  refine ⟨((fun w => (evInf F w n)⁻¹ : Ainf F), ∑ v ∈ S, singleFin v (evFin F v n)⁻¹), ?_⟩
  rw [GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.eSF_eq]
  refine Prod.ext ?_ (af_ext fun u => ?_)
  · funext w
    exact mul_inv_cancel₀ (h1 w)
  · change evalV F u (n.2 * ∑ v ∈ S, singleFin v (evFin F v n)⁻¹) = evalV F u (∑ v ∈ S, singleFin v 1)
    rw [map_mul, GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.evalV_sum, map_sum]
    split_ifs with h
    · rw [Finset.sum_eq_single_of_mem u h (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _), evalV_singleFin_self]
      exact mul_inv_cancel₀ (h2 u h)
    · rw [Finset.sum_eq_zero, mul_zero]
      intro v hv
      exact evalV_singleFin_ne (by rintro rfl; exact h hv) _

theorem evInf_eSF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) :
    evInf F w (eSF S) = 1 := by
  rw [GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.eSF_eq]
  rfl

open Classical in
theorem evFin_eSF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) : evFin F v (eSF S) = if v ∈ S then 1 else 0 := by
  rw [GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.eSF_eq]
  exact GlobalTheory.CompanionTheory.RgEisUnif.EIdemP.evalV_sum S v

theorem compInf_eSF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) :
    compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) (eSF S)) = 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  change (Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E)) _ = 1
  rw [Algebra.TensorProduct.map_tmul, show algebraMap (AF F) (AF F) (eSF S) = eSF S from rfl, evInf_eSF]
  simp [Algebra.TensorProduct.one_def]

open Classical in
theorem compFin_eSF {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) (eSF S)) = if v ∈ S then 1 else 0 := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  change (Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E)) _ = _
  rw [Algebra.TensorProduct.map_tmul, show algebraMap (AF F) (AF F) (eSF S) = eSF S from rfl, evFin_eSF]
  split_ifs <;> simp [Algebra.TensorProduct.one_def]

theorem eq_algebraMap_eSF
    (hc : ∀ (D : D7) (a : AE D), (∀ w, compInf D.host.F D.host.E w a = 0) → (∀ v, cv D v a = 0) → a = 0)
    (D : D7) (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) :
    e = algebraMap (AF D.host.F) (AE D) (eSF S) := by
  classical
  rw [← sub_eq_zero]
  refine hc D _ (fun w => ?_) (fun v => ?_)
  · rw [RingHom.map_sub, he.1 w, compInf_eSF, sub_self]
  · refine (RingHom.map_sub _ _ _).trans ?_
    rw [he.2 v]
    refine sub_eq_zero.2 ?_
    exact (compFin_eSF S v).symm

theorem exists_open_mul_eq_idem :
    (∀ (D : D7) (a : AE D), (∀ w, compInf D.host.F D.host.E w a = 0) → (∀ v, cv D v a = 0) → a = 0) →
    ∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∃ U : Set (AE D), IsOpen U ∧ 1 ∈ U ∧ ∀ x ∈ U, ∃ b, x * b = e := by
  intro hc D S e he
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have hn := continuous_norm (R := AF D.host.F) (A := AE D)
  have cI : ∀ w, Continuous (evInf D.host.F w) := fun w => (continuous_apply w).comp continuous_fst
  have cF : ∀ v, Continuous (evFin D.host.F v) := fun v => (RestrictedProduct.continuous_eval v).comp continuous_snd
  refine ⟨{a | (∀ w, evInf D.host.F w (Algebra.norm (AF D.host.F) a) ≠ 0) ∧
    ∀ v ∈ S, evFin D.host.F v (Algebra.norm (AF D.host.F) a) ≠ 0}, ?_, ?_, ?_⟩
  · have h : {a : AE D | (∀ w, evInf D.host.F w (Algebra.norm (AF D.host.F) a) ≠ 0) ∧
        ∀ v ∈ S, evFin D.host.F v (Algebra.norm (AF D.host.F) a) ≠ 0} =
        (⋂ w, {a : AE D | evInf D.host.F w (Algebra.norm (AF D.host.F) a) ≠ 0}) ∩
        ⋂ v ∈ S, {a : AE D | evFin D.host.F v (Algebra.norm (AF D.host.F) a) ≠ 0} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [h]
    refine (isOpen_iInter_of_finite fun w => ?_).inter (isOpen_biInter_finset fun v _ => ?_)
    · exact isOpen_ne_fun ((cI w).comp hn) continuous_const
    · exact isOpen_ne_fun ((cF v).comp hn) continuous_const
  · simp only [Set.mem_setOf_eq, map_one]
    exact ⟨fun _ => one_ne_zero, fun _ _ => one_ne_zero⟩
  · rintro x ⟨h1, h2⟩
    obtain ⟨c, hxc⟩ := exists_mul_eq_norm (R := AF D.host.F) x
    obtain ⟨m, hm⟩ := exists_mul_eq_eSF S _ h1 h2
    refine ⟨c * algebraMap (AF D.host.F) (AE D) m, ?_⟩
    rw [← mul_assoc, hxc, ← map_mul, hm, eq_algebraMap_eSF hc D S e he]

end GlobalTheory.CompanionTheory.UnitNbhd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintZero
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem IsInt.mul {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s t : Type} [Fintype s]
    {M : Matrix r s (w.adicCompletion E)} {N : Matrix s t (w.adicCompletion E)} (hM : IsInt w M) (hN : IsInt w N) :
    IsInt w (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact (Ov E w).sum_mem fun l _ => (Ov E w).mul_mem (hM i l) (hN l j)

theorem tj_blk (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ϖ : w.adicCompletion E)
    (hϖ : IsUnifV E w ϖ) (k : ℕ) (hk : k ≤ n) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    Tj ℂ n (Ov E w) ϖ k (blk h w m X) =
      if IsInt w m.1.val ∧ IsInt w m.2.val ∧ IsInt w (m.1.val * X) ∧ IsInt w (ϖ • (m.1⁻¹).val) ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧
        IsInt w (ϖ • (X * (m.2⁻¹).val)) ∧ ordL m.1.val.det + ordL m.2.val.det = (k : ℤ) then 1 else 0 := by
  rw [GlobalTheory.T.hecke_indicator_formula E w n k ϖ hϖ hk]
  refine if_congr ?_ rfl rfl
  rw [GlobalTheory.T.block_integral_iff E n a b h w m X, GlobalTheory.T.block_inverse_integral_iff E n a b h w ϖ m X, GlobalTheory.T.block_det_order_add E n a b h w m X]
  tauto

theorem hint_lat (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (ϖ : w.adicCompletion E)
    (hϖ : IsUnifV E w ϖ) (i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) (m : GLw a w × GLw b w)
    (i1 : IsInt w m.1.val) (j2 : IsInt w (ϖ • (m.2⁻¹).val))
    (t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0) (t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0) :
    hint (intMat a b w) (fun X => if IsInt w (m.1.val * Multiplicative.toAdd X) ∧
        IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0) = (qV E w : ℂ) ^ (i * (b - j)) := by
  have hle : intSub a b w ≤ latM ϖ m := fun X hX => by
    refine ⟨i1.mul hX, ?_⟩
    have e : ϖ • (X * (m.2⁻¹).val) = X * (ϖ • (m.2⁻¹).val) := (Matrix.mul_smul _ _ _).symm
    rw [e]
    exact IsInt.mul hX j2
  have := GlobalTheory.T.lattice_indicator_integral_index E a b w (latM ϖ m) hle
  rw [GlobalTheory.T.lattice_index_eq_diagonal E a b w ϖ hϖ i j hi hj m t1 t2, GlobalTheory.T.diagonal_lattice_index_pow E a b w ϖ hϖ i j hi hj] at this
  rw [Nat.cast_pow] at this
  have e2 : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      if IsInt w (m.1.val * Multiplicative.toAdd X) ∧ IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0) =
      fun X => if Multiplicative.toAdd X ∈ latM ϖ m then (1 : ℂ) else 0 :=
    funext fun X => if_congr Iff.rfl rfl rfl
  rw [e2]
  exact this

theorem coef_eq (q : ℕ) (hq : q ≠ 0) (c : ℂˣ) (a b i j : ℕ) (hj : j ≤ b) :
    (c : ℂ) ^ (i * b + j * a) * ((q : ℂ) ^ (-((i : ℂ) * b - (j : ℂ) * a) / 2) * (q : ℂ) ^ (i * (b - j))) = coef q c a b i j := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [coef]
  congr 1
  rw [← Complex.cpow_natCast (q : ℂ), ← Complex.cpow_add _ _ hq']
  congr 1
  push_cast [Nat.cast_sub hj]
  ring

theorem hint_zero {H : Type} [Group H] (K : Subgroup H) : hint K (fun _ : H => (0 : ℂ)) = 0 := by
  unfold hint
  rw [finsum_zero, mul_zero]

set_option maxHeartbeats 1600000 in
theorem ct_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (c : ℂˣ)
    (ϖ : w.adicCompletion E) (hw : IsSplitAt w) (hϖ : IsUnifV E w ϖ) (k : ℕ) (hk : k ≤ n) (m : GLw a w × GLw b w) :
    ctT h w (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c) ϖ k m =
      ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2) := by
  rw [GlobalTheory.T.constant_term_hecke_formula E n a b h w _ ϖ hw hϖ k m]
  by_cases hP : ∃ p ∈ pairs a b k, Tj ℂ a (Ov E w) ϖ p.1 m.1 ≠ 0 ∧ Tj ℂ b (Ov E w) ϖ p.2 m.2 ≠ 0
  · obtain ⟨⟨i, j⟩, hp, h1, h2⟩ := hP
    obtain ⟨hij, hi, hj⟩ : i + j = k ∧ i ≤ a ∧ j ≤ b := by
      exact mem_pairs.1 hp
    simp only at h1 h2
    have c1 := GlobalTheory.T.hecke_indicator_formula E w a i ϖ hϖ hi m.1
    have c2 := GlobalTheory.T.hecke_indicator_formula E w b j ϖ hϖ hj m.2
    rw [c1] at h1
    rw [c2] at h2
    obtain ⟨i1, i2, i3⟩ : IsInt w m.1.val ∧ IsInt w (ϖ • (m.1⁻¹).val) ∧ ordL m.1.val.det = (i : ℤ) := by
      by_contra hc; exact h1 (if_neg hc)
    obtain ⟨j1, j2, j3⟩ : IsInt w m.2.val ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧ ordL m.2.val.det = (j : ℤ) := by
      by_contra hc; exact h2 (if_neg hc)
    have hfun : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) =
        fun X => if IsInt w (m.1.val * Multiplicative.toAdd X) ∧
          IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0 := by
      funext X
      rw [tj_blk E n a b h w ϖ hϖ k hk m]
      have e : ordL m.1.val.det + ordL m.2.val.det = (k : ℤ) := by rw [i3, j3, ← hij]; push_cast; rfl
      by_cases hX : IsInt w (m.1.val * Multiplicative.toAdd X) ∧ IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val))
      · rw [if_pos ⟨i1, j1, hX.1, i2, j2, hX.2, e⟩, if_pos hX]
      · rw [if_neg fun hc => hX ⟨hc.2.2.1, hc.2.2.2.2.2.1⟩, if_neg hX]
    have u1 : Tj ℂ a (Ov E w) ϖ i m.1 = 1 := by rw [c1, if_pos ⟨i1, i2, i3⟩]
    have u2 : Tj ℂ b (Ov E w) ϖ j m.2 = 1 := by rw [c2, if_pos ⟨j1, j2, j3⟩]
    have t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0 := by rw [u1]; exact one_ne_zero
    have t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0 := by rw [u2]; exact one_ne_zero
    rw [hfun, hint_lat E a b w ϖ hϖ i j hi hj m i1 j2 t1 t2, GlobalTheory.T.unramified_character_block_value E a b w c i j m i3 j3, GlobalTheory.T.modulus_half_block_value E a b w i j m i3 j3,
      coef_eq _ (qV_ne_zero w) c a b i j hj, Finset.sum_eq_single_of_mem (⟨i, j⟩ : ℕ × ℕ) hp]
    · simp [u1, u2]
    · rintro ⟨i', j'⟩ hp' hne
      obtain ⟨hij', hi', hj'⟩ : i' + j' = k ∧ i' ≤ a ∧ j' ≤ b := by
        exact mem_pairs.1 hp'
      have : i' ≠ i := fun e => hne (by subst e; congr; omega)
      have u : Tj ℂ a (Ov E w) ϖ i' m.1 = 0 := by
        rw [GlobalTheory.T.hecke_indicator_formula E w a i' ϖ hϖ hi' m.1, if_neg]
        rintro ⟨-, -, e⟩
        exact this (by rw [i3] at e; exact_mod_cast e.symm)
      simp [u]
  · push_neg at hP
    have hz : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) = fun _ => 0 := by
      funext X
      rw [tj_blk E n a b h w ϖ hϖ k hk m, if_neg]
      rintro ⟨i1, j1, -, i2, j2, -, e⟩
      obtain ⟨i, hi, i3⟩ := GlobalTheory.T.det_order_bounded_hecke_support E w a ϖ hϖ m.1 i1 i2
      obtain ⟨j, hj, j3⟩ := GlobalTheory.T.det_order_bounded_hecke_support E w b ϖ hϖ m.2 j1 j2
      have hp : (⟨i, j⟩ : ℕ × ℕ) ∈ pairs a b k := by
        have : i + j = k := by rw [i3, j3] at e; exact_mod_cast e
        exact mem_pairs.2 ⟨this, hi, hj⟩
      have t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0 := by
        rw [GlobalTheory.T.hecke_indicator_formula E w a i ϖ hϖ hi m.1, if_pos ⟨i1, i2, i3⟩]; exact one_ne_zero
      have t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0 := by
        rw [GlobalTheory.T.hecke_indicator_formula E w b j ϖ hϖ hj m.2, if_pos ⟨j1, j2, j3⟩]; exact one_ne_zero
      exact t2 (hP (i, j) hp t1)
    have hs : ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      by_cases t1 : Tj ℂ a (Ov E w) ϖ p.1 m.1 = 0
      · simp [t1]
      · simp [hP p hp t1]
    rw [hz, hs, hint_zero, mul_zero, mul_zero]

theorem ctSat : CtSat := by
  intro E _ _ _ n a b h w ν c V _ _ ρ x Ba Bb hw hν hs ϖ hϖ k hk
  subst hν
  have hF : ctT h w (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c) ϖ k = fun m =>
      ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2) :=
    funext fun m => ct_eq E n a b h w c ϖ hw hϖ k hk m
  rw [hF, GlobalTheory.T.hecke_vector_linear_combination E a b w ϖ hϖ, GlobalTheory.T.satake_eigenvalue_pair_decomposition _ n a b c Ba Bb (qV_ne_zero w) h hs.2.1 hs.2.2.1 k hk, Finset.sum_smul]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨-, hi, hj⟩ : p.1 + p.2 = k ∧ p.1 ≤ a ∧ p.2 ≤ b := by
    exact mem_pairs.1 hp
  rw [hs.2.2.2 ϖ hϖ p.1 hi p.2 hj, smul_smul]

end GlobalTheory.CompanionTheory.CtS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutationStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subquotient_cuspidal_permutation : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l N : ℕ} (x : Fin l → IrrGL k) (hx : ∑ a, (x a).1 = N) (hxc : ∀ a, (x a).IsCusp) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) (h : IsSubquotient π (prodIrr x hx)), ∃ (e : Equiv.Perm (Fin l)) (he : ∑ a, (x (e a)).1 = N), 1 ≤ jm (fun a => x (e a)) he π := by
  first | exact @GlobalTheory.CompanionTheory.SegNcjm.exists_perm_one_le_jm | exact GlobalTheory.CompanionTheory.SegNcjm.exists_perm_one_le_jm | (intros; apply GlobalTheory.CompanionTheory.SegNcjm.exists_perm_one_le_jm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocMIterateDiag
section
open scoped Classical

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail
open PositivityTheory.Rg.BcB.F (LF)

namespace GlobalTheory.CompanionTheory.TailLocPow

theorem hint_fun_zero {H : Type} [Group H] (K : Subgroup H) : hint K (fun _ : H => (0 : ℂ)) = 0 := by
  simp [hint]

theorem rStab_smul {H : Type} [Group H] (c : ℂ) (hc : c ≠ 0) (u : H → ℂ) :
    rStab (fun x => c * u x) = rStab u := by
  ext k
  show (∀ x, c * u (x * k) = c * u x) ↔ (∀ x, u (x * k) = u x)
  exact forall_congr' fun x => mul_right_inj' hc

theorem hint_smul {H : Type} [Group H] (K : Subgroup H) (c : ℂ) (u : H → ℂ) :
    hint K (fun x => c * u x) = c * hint K u := by
  by_cases hc : c = 0
  · subst hc
    simpa using hint_fun_zero K
  · have key : ∀ S : Subgroup H, S = rStab u →
        (((S ⊓ K).relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ (S ⊓ K), c * u q.out =
          c * ((((rStab u ⊓ K).relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ (rStab u ⊓ K), u q.out) := by
      rintro S rfl
      have h : (∑ᶠ q : H ⧸ (rStab u ⊓ K), c * u q.out) = c * ∑ᶠ q : H ⧸ (rStab u ⊓ K), u q.out := by
        simpa only [smul_eq_mul] using (smul_finsum c (fun q : H ⧸ (rStab u ⊓ K) => u q.out)).symm
      rw [h]
      ring
    exact key _ (rStab_smul c hc u)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

variable {k : Type} [Fintype k]

end GlobalTheory.CompanionTheory.TailLocPow

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitalSignAlmostEverywhereStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_sign_almost_everywhere : KapOrbAE := by
  first | exact @GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE | exact GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE | (intros; apply GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE <;> assumption)
end

