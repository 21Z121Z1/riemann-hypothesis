import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0398
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0176
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0303
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetRepsUnipotent
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_fin_coset_reps_of_isDom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G,
      (∀ i, x i ∈ D.J ⊓ D.N) ∧
        ∀ y ∈ D.J, ∃! i, (x i)⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  intro G _ _ _ D t ht
  exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps G D.J
    (D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom) (D.J ⊓ D.N)
    D.isCompact_J (GlobalTheory.CompanionTheory.TopGroup.inter_conj_isOpen G D.J D.isOpen_J (t : G)) inf_le_left inf_le_left
    (exists_mem_inf_conj_of_isDom G D t ht)

end GlobalTheory.CompanionTheory.Casselman
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantIwahoriCosetReps
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_fin_KN_coset_reps
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)) :
    IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) →
    HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ t : Levi k (Bl d), IsDominant k N J d hd t → ∃ r : ℕ, 0 < r ∧
      ∃ x : Fin r → GL (Fin N) k, (∀ i, x i ∈ KN k N J d hd) ∧
        ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈
          J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom := by
  intro hJo hJc hIw hpos t hdom
  have hKN : KN k N J d hd ≤ J := inf_le_left
  exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps (GL (Fin N) k) J
    (J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom) (KN k N J d hd) hJc
    (GlobalTheory.CompanionTheory.TopGroup.inter_conj_isOpen _ J hJo _) inf_le_left hKN
    (exists_mem_KN_inv_mul_mem_inf_map_conj k N h d hd J hJo hJc hIw hpos t hdom)

end GlobalTheory.CompanionTheory.Casselman
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetVolumeFormulaStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_volume_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ m : ℕ, 1 ≤ m → ∀ (p1 p2 : GL (Fin N) k), p1 ∈ KO k (Fin N) → p2 ∈ KO k (Fin N) → ∀ g : Fin (N - 1) → ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {h | ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, h = p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2}) ≤ (Nat.card 𝓀[k] : ENNReal) ^ (∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))) * μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))) := by
  first | exact @GlobalTheory.CompanionTheory.KmVolume.measure_translated_doubleCoset_le | exact GlobalTheory.CompanionTheory.KmVolume.measure_translated_doubleCoset_le | (intros; apply GlobalTheory.CompanionTheory.KmVolume.measure_translated_doubleCoset_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.ZcDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isIrreducible_contra (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) : (contra π).IsIrreducible := by
  exact GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k n) (hA k n V π hs hi) hi

theorem dualCl_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) :
    dualCl x = IrrGL.of (contra x.rep) (isSmooth_contra _) (isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr) := by
  unfold dualCl
  rw [dif_pos (isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr)]

theorem nonempty_equiv_contra_twist (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    {χ χ' : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ') (h : χ * χ' = 1) :
    Nonempty ((twist (contra π) (detChar (Fin n) χ')).Equiv (contra (twist π (detChar (Fin n) χ)))) := by
  have hψ : IsSmoothChar (detChar (Fin n) χ) := hχ.detChar
  have hinv : ∀ g : GL (Fin n) k,
      ((detChar (Fin n) χ' g : ℂˣ) : ℂ) = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) := by
    intro g
    have h1 : χ (Matrix.GeneralLinearGroup.det g) * χ' (Matrix.GeneralLinearGroup.det g) = 1 := by
      rw [← MonoidHom.mul_apply, h, MonoidHom.one_apply]
    have h2 : χ' (Matrix.GeneralLinearGroup.det g) = (χ (Matrix.GeneralLinearGroup.det g))⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    show ((χ' (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) =
      ((χ (Matrix.GeneralLinearGroup.det g⁻¹) : ℂˣ) : ℂ)
    rw [h2, map_inv, map_inv]
  have hdual : ∀ (g : GL (Fin n) k) (l : Module.Dual ℂ V),
      (twist π (detChar (Fin n) χ)).dual g l = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • π.dual g l := by
    intro g l
    apply LinearMap.ext
    intro v
    show l (((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • π g⁻¹ v) = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • l (π g⁻¹ v)
    exact map_smul l _ _
  have hker : ∀ g : GL (Fin n) k, g ∈ (detChar (Fin n) χ).ker →
      ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) = 1 := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [map_inv, hg, inv_one, Units.val_one]
  have hkn : ((detChar (Fin n) χ).ker : Set (GL (Fin n) k)) ∈ nhds (1 : GL (Fin n) k) :=
    IsOpen.mem_nhds hψ (Subgroup.one_mem _)
  have heq : smoothPart π.dual = smoothPart (twist π (detChar (Fin n) χ)).dual := by
    ext l
    constructor
    · intro hl
      apply mem_smoothPart_of_nhds
      refine Filter.mem_of_superset (Filter.inter_mem (IsOpen.mem_nhds hl (by
        show π.dual 1 l = l
        rw [map_one]
        rfl)) hkn) ?_
      rintro g ⟨hg1, hg2⟩
      have h3 : π.dual g l = l := hg1
      show (twist π (detChar (Fin n) χ)).dual g l = l
      rw [hdual, hker g hg2, one_smul]
      exact h3
    · intro hl
      apply mem_smoothPart_of_nhds
      refine Filter.mem_of_superset (Filter.inter_mem (IsOpen.mem_nhds hl (by
        show (twist π (detChar (Fin n) χ)).dual 1 l = l
        rw [map_one]
        rfl)) hkn) ?_
      rintro g ⟨hg1, hg2⟩
      have h3 : (twist π (detChar (Fin n) χ)).dual g l = l := hg1
      rw [hdual, hker g hg2, one_smul] at h3
      show π.dual g l = l
      exact h3
  have htw : ∀ (g : GL (Fin n) k) (l : smoothPart π.dual),
      ((twist (contra π) (detChar (Fin n) χ') g l : smoothPart π.dual) : Module.Dual ℂ V) =
        ((detChar (Fin n) χ' g : ℂˣ) : ℂ) • ((contra π g l : smoothPart π.dual) : Module.Dual ℂ V) :=
    fun _ _ => rfl
  have htw2 : ∀ (g : GL (Fin n) k) (v : V),
      (twist π (detChar (Fin n) χ)) g v = ((detChar (Fin n) χ g : ℂˣ) : ℂ) • π g v :=
    fun _ _ => rfl
  exact ⟨{ toLinearEquiv := LinearEquiv.ofEq _ _ heq
           isIntertwining' := fun g => by
             apply LinearMap.ext
             intro l
             apply Subtype.ext
             apply LinearMap.ext
             intro v
             simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_ofEq_apply, htw,
               LinearMap.smul_apply, contra_apply, htw2, map_smul, smul_eq_mul, hinv] }⟩

private theorem comp_intertwiningMap_mem_smoothPart_dual {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ)
    (l : Module.Dual ℂ W) (hl : l ∈ smoothPart σ.dual) : l ∘ₗ f.toLinearMap ∈ smoothPart ρ.dual := by
  apply mem_smoothPart_of_nhds
  refine Filter.mem_of_superset (IsOpen.mem_nhds hl (by
    show σ.dual 1 l = l
    rw [map_one]
    rfl)) ?_
  intro g hg
  have h : σ.dual g l = l := hg
  show ρ.dual g (l ∘ₗ f.toLinearMap) = l ∘ₗ f.toLinearMap
  refine LinearMap.ext fun v => ?_
  calc (ρ.dual g (l ∘ₗ f.toLinearMap)) v = l (f.toLinearMap (ρ g⁻¹ v)) := rfl
    _ = l (σ g⁻¹ (f v)) := by
      rw [Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.isIntertwining]
    _ = σ.dual g l (f v) := rfl
    _ = (l ∘ₗ f.toLinearMap) v := by
      rw [h, LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply]

private theorem nonempty_contra_equiv_of_equiv {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) :
    Nonempty ((contra σ).Equiv (contra ρ)) := by
  refine ⟨{ toFun := fun l => ⟨l.1 ∘ₗ e.toIntertwiningMap.toLinearMap,
              comp_intertwiningMap_mem_smoothPart_dual e.toIntertwiningMap l.1 l.2⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            invFun := fun l => ⟨l.1 ∘ₗ e.symm.toIntertwiningMap.toLinearMap,
              comp_intertwiningMap_mem_smoothPart_dual e.symm.toIntertwiningMap l.1 l.2⟩
            left_inv := fun l => Subtype.ext (LinearMap.ext fun w => by
              show l.1 (e.toIntertwiningMap.toLinearMap (e.symm.toIntertwiningMap.toLinearMap w)) = l.1 w
              simp only [Representation.IntertwiningMap.toLinearMap_apply,
                Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.apply_symm_apply])
            right_inv := fun l => Subtype.ext (LinearMap.ext fun v => by
              show l.1 (e.symm.toIntertwiningMap.toLinearMap (e.toIntertwiningMap.toLinearMap v)) = l.1 v
              simp only [Representation.IntertwiningMap.toLinearMap_apply,
                Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.symm_apply_apply])
            isIntertwining' := fun g => by
              apply LinearMap.ext
              intro l
              apply Subtype.ext
              apply LinearMap.ext
              intro v
              simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, contra_apply,
                Representation.IntertwiningMap.toLinearMap_apply,
                Representation.IntertwiningMap.isIntertwining] }⟩

theorem dualCl_nu : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s) := by
  intro k _ _ _ _ hA x s
  have hs' : IsSmoothChar (absPow k s) := isSmoothChar_of_isUnram (isUnram_absPow k s)
  have hn' : IsSmoothChar (absPow k (-s)) := isSmoothChar_of_isUnram (isUnram_absPow k (-s))
  have hmul : absPow k s * absPow k (-s) = 1 := by
    rw [absPow_neg, mul_inv_cancel]
  have hψ : IsSmoothChar (detChar (Fin x.fst) (absPow k s)) := hs'.detChar
  have hψn : IsSmoothChar (detChar (Fin x.fst) (absPow k (-s))) := hn'.detChar
  obtain ⟨e1⟩ : Nonempty ((x.nu s).rep.Equiv (twist x.rep (detChar (Fin x.fst) (absPow k s)))) :=
    IrrRep.nonempty_equiv_rep (irrTwist x.snd.rep (detChar (Fin x.fst) (absPow k s)) hψ)
  obtain ⟨e2⟩ := nonempty_contra_equiv_of_equiv e1
  obtain ⟨e3⟩ := nonempty_equiv_contra_twist hA x.rep x.2.rep.smooth x.2.rep.irr hs' hn' hmul
  have hc := isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr
  obtain ⟨e4⟩ := IrrRep.nonempty_equiv_rep
    (⟨_, contra x.rep, isSmooth_contra _, hc⟩ : IrrRep (GL (Fin x.fst) k))
  have e5 := twistEquiv e4 (detChar (Fin x.fst) (absPow k (-s)))
  rw [dualCl_eq hA, dualCl_eq hA]
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  exact IrrRep.cl_eq_iff.mpr ⟨(e2.symm.trans e3.symm).trans e5.symm⟩

end GlobalTheory.CompanionTheory.ZcDual

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAlgHomMulEquivDec
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.DecGal

theorem exists_algHom_mulEquiv_dec : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∃ (ι : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F)) (e : (AlgebraicClosure (v.adicCompletion F) ≃ₐ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F)) ≃* Dec (F := F) A), Continuous e ∧ Continuous e.symm ∧ ∀ σ x, ι (((e σ : Dec (F := F) A) : G F Ω) x) = σ (ι x) := by
  intro F Ω _ _ _ _ _ A v h
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb F Ω A v h
  obtain ⟨θ, hθ, hθ', hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc F Ω A v h ι hι
  refine ⟨ι, θ.symm, hθ', hθ, fun σ x => ?_⟩
  have := hl (θ.symm σ) x
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.CompanionTheory.DecGal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCliffordLowestVector
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.CliffModel

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

def IsCAR {M ι : Type} [DecidableEq M] [Fintype ι] [DecidableEq ι] (A : M → Matrix ι ι ℂ) : Prop :=
  (∀ p r, A p * A r + A r * A p = 0) ∧
    ∀ p r, A p * (A r)ᴴ + (A r)ᴴ * A p = if p = r then 1 else 0

def annM : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

def parM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def vacM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

theorem annM_sq : annM * annM = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [annM, Matrix.mul_apply, Fin.sum_univ_two]

theorem annM_conj : annMᴴ = !![0, 0; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [annM, Matrix.conjTranspose_apply]

theorem annM_car : annM * annMᴴ + annMᴴ * annM = 1 := by
  rw [annM_conj]
  ext i j; fin_cases i <;> fin_cases j <;> simp [annM, Matrix.mul_apply, Fin.sum_univ_two]

theorem parM_sq : parM * parM = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [parM, Matrix.mul_apply, Fin.sum_univ_two]

theorem parM_herm : parMᴴ = parM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [parM, Matrix.conjTranspose_apply]

theorem parM_annM : parM * annM + annM * parM = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [parM, annM, Matrix.mul_apply, Fin.sum_univ_two]

theorem annM_vacM : annM * vacM = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [annM, vacM, Matrix.mul_apply, Fin.sum_univ_two]

theorem vacM_ne : vacM ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [vacM] at this

theorem exists_fock (m : ℕ) : ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
    (A : Fin m → Matrix ι ι ℂ) (G Q : Matrix ι ι ℂ),
    IsCAR A ∧ G * G = 1 ∧ Gᴴ = G ∧ (∀ p, G * A p + A p * G = 0) ∧ Q ≠ 0 ∧ ∀ p, A p * Q = 0 := by
  induction m with
  | zero =>
    refine ⟨Unit, inferInstance, inferInstance, fun p => p.elim0, 1, 1, ⟨fun p => p.elim0, fun p => p.elim0⟩,
      by simp, by simp, fun p => p.elim0, one_ne_zero, fun p => p.elim0⟩
  | succ m ih =>
    obtain ⟨ι, _, _, A, G, Q, ⟨h1, h2⟩, hG, hGh, hGA, hQ, hv⟩ := ih
    have hGAh : ∀ i, G * (A i)ᴴ + (A i)ᴴ * G = 0 := by
      intro i
      have := congrArg conjTranspose (hGA i)
      simpa [conjTranspose_add, conjTranspose_mul, hGh, add_comm] using this
    refine ⟨ι × Fin 2, inferInstance, inferInstance,
      Fin.cases (G ⊗ₖ annM) (fun i => A i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)),
      G ⊗ₖ parM, Q ⊗ₖ vacM, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro p r
      induction p using Fin.cases with
      | zero =>
        induction r using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero, ← mul_kronecker_mul, annM_sq, kronecker_zero, add_zero]
        | succ r =>
          simp only [Fin.cases_zero, Fin.cases_succ, ← mul_kronecker_mul, mul_one, one_mul,
            ← add_kronecker, hGA, zero_kronecker]
      | succ p =>
        induction r using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero, Fin.cases_succ, ← mul_kronecker_mul, mul_one, one_mul,
            ← add_kronecker]
          rw [add_comm, hGA, zero_kronecker]
        | succ r =>
          simp only [Fin.cases_succ, ← mul_kronecker_mul, mul_one, ← add_kronecker, h1,
            zero_kronecker]
    · intro p r
      induction p using Fin.cases with
      | zero =>
        induction r using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero, conjTranspose_kronecker, hGh, ← mul_kronecker_mul, hG,
            ← kronecker_add, annM_car, if_true, one_kronecker_one]
        | succ r =>
          have hne : (0 : Fin (m + 1)) ≠ r.succ := (Fin.succ_ne_zero r).symm
          simp only [Fin.cases_zero, Fin.cases_succ, conjTranspose_kronecker, conjTranspose_one,
            ← mul_kronecker_mul, mul_one, one_mul, ← add_kronecker, hGAh, zero_kronecker, if_neg hne]
      | succ p =>
        induction r using Fin.cases with
        | zero =>
          have hne : p.succ ≠ (0 : Fin (m + 1)) := Fin.succ_ne_zero p
          simp only [Fin.cases_zero, Fin.cases_succ, conjTranspose_kronecker, hGh,
            ← mul_kronecker_mul, mul_one, one_mul, ← add_kronecker, if_neg hne]
          rw [add_comm, hGA, zero_kronecker]
        | succ r =>
          simp only [Fin.cases_succ, conjTranspose_kronecker, conjTranspose_one,
            ← mul_kronecker_mul, mul_one, ← add_kronecker, h2, Fin.succ_inj]
          split_ifs <;> simp
    · rw [← mul_kronecker_mul, hG, parM_sq, one_kronecker_one]
    · rw [conjTranspose_kronecker, hGh, parM_herm]
    · intro p
      induction p using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, ← mul_kronecker_mul, hG, ← kronecker_add, parM_annM, kronecker_zero]
      | succ p =>
        simp only [Fin.cases_succ, ← mul_kronecker_mul, mul_one, one_mul, ← add_kronecker, hGA,
          zero_kronecker]
    · intro h
      apply hQ
      ext i j
      have := congrFun (congrFun h (i, 0)) (j, 0)
      simpa [vacM, kroneckerMap_apply] using this
    · intro p
      induction p using Fin.cases with
      | zero => simp only [Fin.cases_zero, ← mul_kronecker_mul, annM_vacM, kronecker_zero]
      | succ p => simp only [Fin.cases_succ, ← mul_kronecker_mul, hv, zero_kronecker]

theorem car_lin {M ι : Type} [DecidableEq M] [Fintype ι] [DecidableEq ι] {A : M → Matrix ι ι ℂ}
    (hA : IsCAR A) (x y u v : ℂ) (p r : M) :
    (x • A p + y • (A p)ᴴ) * (u • A r + v • (A r)ᴴ) + (u • A r + v • (A r)ᴴ) * (x • A p + y • (A p)ᴴ) =
      (if p = r then x * v + y * u else 0) • (1 : Matrix ι ι ℂ) := by
  obtain ⟨h1, h2⟩ := hA
  have h3 : (A p)ᴴ * (A r)ᴴ + (A r)ᴴ * (A p)ᴴ = 0 := by
    have := congrArg conjTranspose (h1 p r)
    simpa [conjTranspose_add, conjTranspose_mul, add_comm] using this
  have key : (x • A p + y • (A p)ᴴ) * (u • A r + v • (A r)ᴴ) + (u • A r + v • (A r)ᴴ) * (x • A p + y • (A p)ᴴ) =
      (x * u) • (A p * A r + A r * A p) + (x * v) • (A p * (A r)ᴴ + (A r)ᴴ * A p) +
        (y * u) • (A r * (A p)ᴴ + (A p)ᴴ * A r) + (y * v) • ((A p)ᴴ * (A r)ᴴ + (A r)ᴴ * (A p)ᴴ) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    module
  rw [key, h1, h2, h2, h3]
  by_cases h : p = r
  · subst h
    simp [add_smul]
  · simp [h, Ne.symm h]

def coefA {n : ℕ} (s : ℂ) (a b : Fin n) : ℂ := if a < b then 0 else if b < a then s else 1

def coefC {n : ℕ} (s : ℂ) (a b : Fin n) : ℂ := if a < b then s else if b < a then 0 else 1

def modeOf {n : ℕ} (a b : Fin n) : Fin n × Fin n := (min a b, max a b)

theorem modeOf_comm {n : ℕ} (a b : Fin n) : modeOf a b = modeOf b a := by
  simp [modeOf, min_comm, max_comm]

theorem modeOf_lt {n : ℕ} {a b : Fin n} (h : a < b) : modeOf a b = (a, b) := by
  simp [modeOf, min_eq_left h.le, max_eq_right h.le]

theorem modeOf_gt {n : ℕ} {a b : Fin n} (h : b < a) : modeOf a b = (b, a) := by
  simp [modeOf, min_eq_right h.le, max_eq_left h.le]

theorem modeOf_self {n : ℕ} (a : Fin n) : modeOf a a = (a, a) := by
  simp [modeOf]

theorem coef_rel {n : ℕ} {s : ℂ} (hs : s * s = 2) (a b d e : Fin n) :
    (if modeOf a b = modeOf d e then coefA s a b * coefC s d e + coefC s a b * coefA s d e else 0) =
      if a = e ∧ b = d then 2 else 0 := by
  rcases lt_trichotomy a b with hab | rfl | hab <;> rcases lt_trichotomy d e with hde | rfl | hde
  · have : ¬ (a = e ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hde
    simp [coefA, coefC, hab, hde, lt_asymm hab, lt_asymm hde, this]
  · have h1 : ¬ (a = d ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hab
    simp [modeOf_lt hab, modeOf_self, h1]
  · simp only [modeOf_lt hab, modeOf_gt hde, Prod.mk.injEq, coefA, coefC, hab, hde, lt_asymm hab,
      lt_asymm hde, if_true, if_false]
    simp [hs]
  · have h1 : ¬ (a = e ∧ a = d) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hde
    have h2 : ¬ (a = d ∧ a = e) := fun h => h1 ⟨h.2, h.1⟩
    simp [modeOf_lt hde, modeOf_self, h1, h2]
  · simp only [modeOf_self, Prod.mk.injEq, coefA, coefC, lt_irrefl, if_false, and_self]
    split_ifs <;> norm_num
  · have h1 : ¬ (a = e ∧ a = d) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hde
    have h3 : ¬ (a = d ∧ a = e) := fun h => h1 ⟨h.2, h.1⟩
    simp [modeOf_gt hde, modeOf_self, h1, h3]
  · simp only [modeOf_gt hab, modeOf_lt hde, Prod.mk.injEq, coefA, coefC, hab, hde, lt_asymm hab,
      lt_asymm hde, if_true, if_false]
    by_cases h : b = d ∧ a = e
    · simp [h, hs]
    · have h' : ¬ (a = e ∧ b = d) := fun g => h ⟨g.2, g.1⟩
      simp [h, h']
  · have h1 : ¬ (a = d ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hab
    have h2 : ¬ (b = d ∧ a = d) := fun h => h1 ⟨h.2, h.1⟩
    simp [modeOf_gt hab, modeOf_self, h1, h2]
  · have : ¬ (a = e ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hde
    simp [coefA, coefC, hab, hde, lt_asymm hab, lt_asymm hde, this]

theorem star_coefC {n : ℕ} {s : ℂ} (hs : star s = s) (a b : Fin n) :
    star (coefC s a b) = coefA s b a := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [coefA, coefC, h, lt_asymm h, hs]
  · simp [coefA, coefC]
  · simp [coefA, coefC, h, lt_asymm h]

theorem star_coefA {n : ℕ} {s : ℂ} (hs : star s = s) (a b : Fin n) :
    star (coefA s a b) = coefC s b a := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [coefA, coefC, h, lt_asymm h]
  · simp [coefA, coefC]
  · simp [coefA, coefC, h, lt_asymm h, hs]

theorem exists_cliff_model : ∀ n : ℕ, ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
    (c : Fin n → Fin n → Matrix ι ι ℂ),
    IsCliff c ∧ ∃ q : ι → ℂ, q ≠ 0 ∧ ∀ a b, a < b → c b a *ᵥ q = 0 := by
  intro n
  obtain ⟨ι, _, _, A0, G, Q, ⟨h1, h2⟩, -, -, -, hQ, hv⟩ :=
    exists_fock (Fintype.card (Fin n × Fin n))
  let e := Fintype.equivFin (Fin n × Fin n)
  let A : Fin n × Fin n → Matrix ι ι ℂ := fun p => A0 (e p)
  have hA : IsCAR A := ⟨fun p r => h1 _ _, fun p r => by simp [A, h2, e.injective.eq_iff]⟩
  let s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
  have hs : s * s = 2 := by
    simp only [s, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hs' : star s = s := Complex.conj_ofReal _
  refine ⟨ι, inferInstance, inferInstance,
    fun a b => coefA s a b • A (modeOf a b) + coefC s a b • (A (modeOf a b))ᴴ, ⟨?_, ?_⟩, ?_⟩
  · intro a b d e'
    rw [car_lin hA, coef_rel hs]
    split_ifs
    · simp [two_smul, one_add_one_eq_two]
    · simp
  · intro a b
    simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_conjTranspose, star_coefA hs',
      star_coefC hs', modeOf_comm a b]
    rw [add_comm]
  · obtain ⟨i, j, hij⟩ : ∃ i j, Q i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hQ (by ext i j; exact h i j)
    refine ⟨fun i => Q i j, fun h => hij (congrFun h i), ?_⟩
    intro a b hab
    have hcol : ∀ M : Matrix ι ι ℂ, M * Q = 0 → M *ᵥ (fun i => Q i j) = 0 := by
      intro M hM
      funext k
      have := congrFun (congrFun hM k) j
      simpa [Matrix.mul_apply, mulVec, dotProduct] using this
    apply hcol
    simp only [coefA, coefC, hab, lt_asymm hab, if_true, if_false, zero_smul, add_zero,
      smul_mul_assoc]
    simp [A, hv]

end GlobalTheory.CompanionTheory.CliffModel
end
end

