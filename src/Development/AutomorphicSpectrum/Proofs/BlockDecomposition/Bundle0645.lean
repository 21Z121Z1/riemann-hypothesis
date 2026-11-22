import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0485
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0226
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationFourierCoefficient
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellVal

section Blocks

variable {R : Type} [CommRing R] {n r t : ℕ} (hn : r + t = n)

theorem block_mul₂ (a a' : Matrix (Fin r) (Fin r) R) (b b' : Matrix (Fin r) (Fin t) R)
    (c c' : Matrix (Fin t) (Fin r) R) (d d' : Matrix (Fin t) (Fin t) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one : bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 1 = 1 := by
  simp only [bl]
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrix_zero : bl hn (0 : Matrix (Fin r) (Fin r) R) 0 0 0 = 0 := by
  simp only [bl, Matrix.fromBlocks_zero]
  rfl

theorem det_bl_unip (y : Matrix (Fin r) (Fin t) R) : (bl hn 1 y 0 1).det = 1 := by
  simp only [bl]
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem trace_bl_last (b : Matrix (Fin t) (Fin t) R) (Z : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (bl hn 0 0 0 b * Z) =
      Matrix.trace (b * Z.submatrix (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr)
        (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr)) := by
  set e := finSumFinEquiv.trans (finCongr hn) with he
  have h1 : Z = (Matrix.fromBlocks (Z.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)) (Z.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr))
      (Z.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)) (Z.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr))).submatrix e.symm e.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp
  conv_lhs => rw [h1]
  simp only [bl, ← he]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  rw [Equiv.sum_comp e.symm (fun s => Matrix.fromBlocks _ _ _ _ s s), Fintype.sum_sum_type]
  simp

end Blocks

section Frames

variable {D : D7} {a n r t : ℕ} (hn : r + t = n)

theorem jn_mul_unip (x : Mx D a r) (y : Mx D r t) :
    (HMul.hMul (jn hn x 0) (bl hn 1 y 0 1) : Mx D a n) = jn hn x (mm x y) := by
  simp only [jn, bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp [mm]

theorem trace_inner_jn (V : HSp D) (b : Mx D t t) (x : Mx D V.rank r) (v : Mx D V.rank t) :
    Matrix.trace (HMul.hMul (bl hn 0 0 0 b) (GlobalTheory.StdUnn.inner V (jn hn x v) (jn hn x v)) : Mx D n n) =
      Matrix.trace (mm b (ip V v v)) := by
  rw [trace_bl_last]
  congr 1
  have h : (GlobalTheory.StdUnn.inner V (jn hn x v) (jn hn x v)).submatrix (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr)
      (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr) = ip V v v := by
    ext i j
    simp [GlobalTheory.StdUnn.inner, ip, mm, jn, adj, Matrix.mul_apply]
  rw [h]

def unipGL (y : Mx D r t) : GL (Fin n) (AE D) where
  val := bl hn 1 y 0 1
  inv := bl hn 1 (-y) 0 1
  val_inv := by rw [block_mul₂]; simpa using blockRowSubstitution_one hn
  inv_val := by rw [block_mul₂]; simpa using blockRowSubstitution_one hn

theorem det_unipGL (y : Mx D r t) :
    Matrix.GeneralLinearGroup.det (unipGL hn y : GL (Fin n) (AE D)) = (1 : (AE D)ˣ) :=
  Units.ext (det_bl_unip hn y)

theorem adj_bl_unip_neg (y : Mx D r t) :
    adj (bl hn (1 : Mx D r r) (-y) 0 (1 : Mx D t t)) = bl hn (1 : Mx D r r) 0 (-adj y) (1 : Mx D t t) := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [adj, bl, Matrix.one_apply, apply_ite (cA D)]
  all_goals by_cases h : i = j <;> simp [h, eq_comm]

end Frames

theorem weil_translate_frame {D : D7} {n r t : ℕ} (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (V : HSp D)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ)
    (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)}
    (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕)
    {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (Φ : schwartzA θ V.rank n)
    {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t) (y : Mx D r t)
    (x : Mx D V.rank r) :
    (ω (M.sh y * M.emb (w * nb b) * 1) Φ).1 (jn hn x 0) =
      ∫ v, pch ψ b.1 (ip V v v) * Φ.1 (jn hn x v) * ψ (trA (Matrix.trace (ip V (mm x y) v))) ∂μt := by
  have e1 : ω (M.sh y * M.emb (w * nb b) * 1) Φ = ω (M.sh y) (ω (M.emb w) (ω (M.emb (nb b)) Φ)) := by
    simp only [mul_one, map_mul, Module.End.mul_apply]
  have hdet := det_unipGL hn y
  have hsh : mat (M.sh y) = blk4 (unipGL hn y).1 0 0 (adj ((unipGL hn y)⁻¹).1) := by
    rw [M.sh_mat]
    have : ((unipGL hn y)⁻¹).1 = bl hn 1 (-y) 0 1 := rfl
    rw [this, adj_bl_unip_neg]
    rfl
  have hemb : mat (M.emb (nb b)) = blk4 1 (bl hn 0 0 0 b.1) 0 1 := by
    rw [M.emb_mat (nb b) 1 b.1 0 1 (hnb b), blockRowSubstitution_one, blockMatrix_zero]
  rw [e1, hω.levi (M.sh y) (unipGL hn y) hsh, hdet]
  have hpow : npow (absA D 1) ((V.rank : ℂ) / 2) = 1 := by simp [npow]
  rw [map_one, hpow]
  simp only [Circle.coe_one, one_mul]
  have hj : (HMul.hMul (jn hn x 0) (unipGL hn y).1 : Mx D V.rank n) = jn hn x (mm x y) := jn_mul_unip hn x y
  rw [hj, (hP D n r t hn M V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr μt hμr hμt (ω (M.emb (nb b)) Φ)).2.2 w hw x (mm x y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [hω.unip (M.emb (nb b)) _ hemb, trace_inner_jn]
  rfl

end GlobalTheory.CompanionTheory.CellVal

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockInjectiveIrreducible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.BZNuPair.WhitSub

theorem exists_injective_of_subQuot_bot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} (hσ : σ.IsIrreducible) {ρ : Representation ℂ G V}
    (A B : Subrepresentation ρ) (hB : B = ⊥) (f : σ.IntertwiningMap (subQuot A B))
    (hf : f.toLinearMap ≠ 0) : ∃ g : σ.IntertwiningMap ρ, Function.Injective g := by
  subst hB
  have hle : (⊥ : Subrepresentation ρ).toSubmodule.comap A.toSubmodule.subtype ≤
      LinearMap.ker A.toSubmodule.subtype := fun v hv => by
    have : (v : V) ∈ (⊥ : Subrepresentation ρ).toSubmodule := hv
    exact this
  let p : (subQuot A ⊥).IntertwiningMap ρ :=
    .mk (Submodule.liftQ _ A.toSubmodule.subtype hle) (fun g => by
      ext v
      rfl)
  have hp : Function.Injective p := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 hx
  have hi : Function.Injective (p.comp f) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    rcases eq_bot_or_eq_top (p.comp f).ker with h | h
    · have : x ∈ (p.comp f).ker := hx
      rw [h] at this
      exact this
    · exfalso
      refine hf (LinearMap.ext fun y => ?_)
      have hy : y ∈ (p.comp f).ker := by rw [h]; trivial
      exact hp (by simpa using hy)
  exact ⟨p.comp f, hi⟩

theorem exists_irr_sub : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → Nontrivial (X ⧸ whitKer ψ d J) →
    ∃ (S : IrrRep (GL (Fin (d 0)) k)) (f : S.ρ.IntertwiningMap (whit2 ψ d J)), Function.Injective f := by
  intro k _ _ _ _ ψ _ d X _ _ J hs hfl hnt
  obtain ⟨hgt, hlt⟩ := (hasFiniteLength_iff_wellFounded J).1 hfl
  have hbotImg : whitImg ψ d J ⊥ = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.map_bot _
  have htop : whitImg ψ d J ⊤ ≠ ⊥ := by
    intro h
    have h1 : (whitImg ψ d J ⊤).toSubmodule = ⊤ := by
      show (⊤ : Subrepresentation J).toSubmodule.map (whitKer ψ d J).mkQ = ⊤
      exact (Submodule.map_top _).trans (Submodule.range_mkQ _)
    rw [h] at h1
    obtain ⟨x, hx⟩ := exists_ne (0 : X ⧸ whitKer ψ d J)
    have : x ∈ (⊥ : Subrepresentation (whit2 ψ d J)).toSubmodule := by rw [h1]; trivial
    exact hx this
  obtain ⟨T, hT, hmin⟩ := (wellFounded_lt (α := Subrepresentation J)).has_min
    {T | whitImg ψ d J T ≠ ⊥} ⟨⊤, htop⟩
  have hbot : (⊥ : Subrepresentation J) < T := by
    refine bot_lt_iff_ne_bot.2 fun h => hT ?_
    rw [h]
    exact hbotImg
  obtain ⟨T', hT', hmax⟩ := (wellFounded_gt (α := Subrepresentation J)).has_min
    {B | B < T} ⟨⊥, hbot⟩
  have hcov : T' ⋖ T := ⟨hT', fun C hBC hCA => hmax C hCA hBC⟩
  have hImg' : whitImg ψ d J T' = ⊥ := by
    by_contra h
    exact hmin T' h hT'
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨_, subQuot T T', IsSubquotient.isSmooth ⟨T, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩ hs, isIrreducible_subQuot hcov⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
    k (Fin 2) (fun a => Fin (d a)) τ
  have hspan := GlobalTheory.T.whittaker_subquotient_equiv k ψ d X J T T' (fun a => (s a).V) (fun a => (s a).ρ) hT'.le Φ
  have hQ : Nontrivial ((whitImg ψ d J T).toSubmodule ⧸
      (whitImg ψ d J T').toSubmodule.comap (whitImg ψ d J T).toSubmodule.subtype) := by
    refine Submodule.Quotient.nontrivial_iff.2 fun h => hT ?_
    apply Subrepresentation.toSubmodule_injective
    refine le_antisymm (fun x hx => ?_) bot_le
    have hx' : (⟨x, hx⟩ : (whitImg ψ d J T).toSubmodule) ∈
        (whitImg ψ d J T').toSubmodule.comap (whitImg ψ d J T).toSubmodule.subtype := by
      rw [h]; trivial
    rw [Submodule.mem_comap, hImg'] at hx'
    exact hx'
  obtain ⟨f, hf⟩ : ∃ f : (s 0).ρ.IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')),
      f.toLinearMap ≠ 0 := by
    by_contra hno
    push_neg at hno
    have : (⨆ f : (s 0).ρ.IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')),
        LinearMap.range f.toLinearMap) = ⊥ := by
      refine le_antisymm (iSup_le fun f => ?_) bot_le
      rw [hno f, LinearMap.range_zero]
    rw [this] at hspan
    exact bot_ne_top hspan
  obtain ⟨g, hg⟩ := exists_injective_of_subQuot_bot (s 0).irr _ _ hImg' f hf
  exact ⟨s 0, g, hg⟩

end GlobalTheory.CompanionTheory.BZNuPair.WhitSub

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockSubquotientTensor
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.BZNuPair

theorem whit2_isSubquotient_whitImg_top {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Type} [AddCommGroup X]
    [Module ℂ X] (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    IsSubquotient (whit2 ψ d J) (whitImg ψ d J ⊤).toRepresentation := by
  let f : (whitImg ψ d J ⊤).toRepresentation.IntertwiningMap (whit2 ψ d J) :=
    ⟨(whitImg ψ d J ⊤).toSubmodule.subtype, fun _ => rfl⟩
  refine .of_surjective f fun w => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact ⟨⟨Submodule.Quotient.mk x, x, trivial, rfl⟩, rfl⟩

theorem not_isSubquotient_whitImg_bot {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X W : Type} [AddCommGroup X]
    [Module ℂ X] [AddCommGroup W] [Module ℂ W] (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    {σ : Representation ℂ (GL (Fin (d 0)) k) W} (hσ : σ.IsIrreducible) :
    ¬ IsSubquotient σ (whitImg ψ d J ⊥).toRepresentation := by
  rintro ⟨R, f, hf⟩
  have := nontrivial_of_irreducible hσ
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf w
  have hv : v = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨t, ht, h⟩ := v.1.2
    have ht0 : t = 0 := ht
    rw [← h, ht0]
    simp
  exact hw (by rw [hv, map_zero])

theorem exists_constituent_of_whit2 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → ∀ S : IrrRep (GL (Fin (d 0)) k),
    IsSubquotient S.ρ (whit2 ψ d J) → ∃ s : ∀ a, IrrRep (GL (Fin (d a)) k),
      IsSubquotient (piTensor fun a => (s a).ρ) J ∧ Nonempty ((s 0).ρ.Equiv S.ρ) := by
  intro k _ _ _ _ ψ _ d X _ _ J hs hfl S hS
  obtain ⟨hgt, hlt⟩ := (hasFiniteLength_iff_wellFounded J).1 hfl
  obtain ⟨T, hT, hmin⟩ := WellFounded.has_min hlt.wf
    {T : Subrepresentation J | IsSubquotient S.ρ (whitImg ψ d J T).toRepresentation}
    ⟨⊤, hS.trans (whit2_isSubquotient_whitImg_top ψ d J)⟩
  have hne : T ≠ ⊥ := by
    rintro rfl
    exact not_isSubquotient_whitImg_bot ψ d J S.irr hT
  obtain ⟨T', hT'lt, hmax⟩ := WellFounded.has_min hgt.wf {U : Subrepresentation J | U < T}
    ⟨⊥, bot_lt_iff_ne_bot.2 hne⟩
  have hcov : T' ⋖ T := ⟨hT'lt, fun c h1 h2 => hmax c h2 h1⟩
  have hq : IsSubquotient (subQuot T T') J :=
    ⟨T, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨_, subQuot T T', hq.isSmooth hs, isIrreducible_subQuot hcov⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k (Fin 2)
    (fun a => Fin (d a)) τ
  have hspan := GlobalTheory.T.whittaker_subquotient_equiv k ψ d X J T T' (fun a => (s a).V) (fun a => (s a).ρ) hT'lt.le Φ
  refine ⟨s, (IsSubquotient.of_surjective Φ.toIntertwiningMap Φ.surjective).trans hq, ?_⟩
  rcases GlobalTheory.T.irreducible_subquotient_of_extension _ _ _ (whit2 ψ d J) S.ρ _ _ (whitImg_mono ψ d J hT'lt.le) S.irr hT with h | h
  · exact absurd hT'lt (hmin T' h)
  · obtain ⟨e⟩ := GlobalTheory.T.subquotient_equiv_of_irreducible_image _ _ _ _ (s 0).ρ _ S.ρ (s 0).irr S.irr hspan h
    exact ⟨e.symm⟩

end GlobalTheory.CompanionTheory.BZNuPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroCoefficientTotal
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

variable {D : D7} {p : ℕ}

theorem mx_zero_subsingleton : Subsingleton (Mx D 0 p) :=
  ⟨fun _ _ => funext fun i => i.elim0⟩

theorem one_mem_schwartzA_zero (θ : InfFam D) : (fun _ => 1 : Mx D 0 p → ℂ) ∈ schwartzA θ 0 p := by
  refine Submodule.subset_span ?_
  let f : SchwartzMap (D.what₂.Tau → Fin 0 → Fin p → ℂ) ℂ :=
    { toFun := fun _ => 1
      smooth' := contDiff_const
      decay' := by
        intro k n
        refine ⟨1, fun x => ?_⟩
        have hx : x = 0 := Subsingleton.elim _ _
        subst hx
        rcases k with _ | k
        · rcases n with _ | n
          · simp
          · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
        · simp }
  refine ⟨f, fun _ => 1, ⟨IsLocallyConstant.const 1, ?_⟩, ?_⟩
  · exact (Set.subsingleton_of_subsingleton).isCompact
  · funext x
    exact (mul_one (1 : ℂ)).symm

theorem pr_zero (b₀ : HermE D 0) (x y : Mx D 0 p) : pr b₀ x y = 0 := by
  ext i j
  simp [pr, HMul.hMul]

theorem isTh_one {μ : Measure (Mx D 0 p)} (h1 : μ Set.univ = 1) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (b₀ : HermE D 0) : IsTh ψ 1 θ b₀ μ (fun _ _ => 1) := by
  have : IsProbabilityMeasure μ := ⟨h1⟩
  refine ⟨fun _ => one_mem_schwartzA_zero θ, continuous_const, ?_, ?_, ?_, ?_⟩
  · intro C _
    exact ⟨_, one_mem_schwartzA_zero θ, fun _ _ _ => le_rfl⟩
  · intro g a _ h y
    simp [npow]
  · intro g b _ h y
    simp [pr_zero, halfTr]
  · intro g _ h x
    simp [pr_zero]

theorem zeroTotal : ZeroTotal := by
  intro D p μ 𝓕 h ψ hψ b₀ θ hθ u hu hB hall
  have hs : Subsingleton (Mx D 0 p) := mx_zero_subsingleton
  obtain ⟨-, -, hF⟩ := h
  have hne : 𝓕.Nonempty := by
    rcases Set.eq_empty_or_nonempty 𝓕 with he | hn
    · simp [he] at hF
    · exact hn
  have huniv : 𝓕 = Set.univ := by
    obtain ⟨y, hy⟩ := hne
    exact Set.eq_univ_of_forall fun z => (Subsingleton.elim z y) ▸ hy
  have h1 : μ Set.univ = 1 := huniv ▸ hF
  have : IsProbabilityMeasure μ := ⟨h1⟩
  have h0 := hall _ (isTh_one h1 ψ θ b₀)
  have hc : (fun y => u y * conj (1 : ℂ)) = fun _ => u 0 := by
    funext y
    simp [Subsingleton.elim y 0]
  have h2 : u 0 = 0 := by
    have h3 : ∫ y, u y * conj (1 : ℂ) ∂μ = 0 := h0
    rw [hc] at h3
    simpa using h3
  funext y
  rw [Subsingleton.elim y 0, h2]
  rfl

end GlobalTheory.CompanionTheory.ThTot

end
end

