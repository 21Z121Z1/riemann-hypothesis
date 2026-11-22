import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0022
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0070
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0124
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0071

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibre
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

def topR (e : c ⊕ d ≃ b) (y : Matrix c a k) : Matrix b a k := (fromRows y 0).submatrix e.symm id

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
@[simp] theorem topR_inl (e : c ⊕ d ≃ b) (y : Matrix c a k) (i : c) (l : a) :
    topR e y (e (.inl i)) l = y i l := by
  simp [topR]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
@[simp] theorem topR_inr (e : c ⊕ d ≃ b) (y : Matrix c a k) (i : d) (l : a) :
    topR e y (e (.inr i)) l = 0 := by
  simp [topR]

theorem mul_topR (e : c ⊕ d ≃ b) (g : Matrix b b k) (y : Matrix c a k) (i : b) (l : a) :
    (g * topR e y) i l = ∑ m, g i (e (.inl m)) * y m l := by
  rw [mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simp

theorem topR_mul (e : c ⊕ d ≃ b) (y : Matrix c a k) (g : Matrix a a k) :
    topR e (y * g) = topR e y * g := by
  ext i l
  obtain ⟨i | i, rfl⟩ := e.surjective i <;> simp [mul_apply]

theorem rank_topR (e : c ⊕ d ≃ b) (y : Matrix c a k) : (topR e y).rank = y.rank := by
  refine le_antisymm ?_ ?_
  · have h : topR e y = ((1 : Matrix b b k).submatrix id fun i => e (.inl i)) * y := by
      ext i l
      obtain ⟨i | i, rfl⟩ := e.surjective i
      · simp [mul_apply, one_apply]
      · simp [mul_apply, one_apply]
    rw [h]
    exact rank_mul_le_right _ _
  · have h : (topR e y).submatrix (fun i => e (.inl i)) (Equiv.refl a) = y := by
      ext i l; simp
    have h2 := rank_submatrix_le (topR e y) (fun i => e (.inl i)) (Equiv.refl a)
    rwa [h] at h2

def topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} (y : RankIn k a c {κ}) : RankIn k a b {κ} :=
  ⟨topR e y.1, (rank_topR e y.1).trans y.2⟩

theorem range_topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} :
    Set.range (topEmbR (k := k) (a := a) e (κ := κ)) = {x | ∀ j i, x.1 (e (.inr j)) i = 0} := by
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, rfl⟩ j i
    exact topR_inr e _ j i
  · have hxy : x.1 = topR e (x.1.submatrix (fun i => e (.inl i)) id) := by
      ext i l
      obtain ⟨i | i, rfl⟩ := e.surjective i
      · simp
      · simpa using hx i l
    have hr : (x.1.submatrix (fun i => e (.inl i)) id).rank = κ := by
      rw [← rank_topR e, ← hxy]
      exact x.2
    exact ⟨⟨_, hr⟩, Subtype.ext hxy.symm⟩

theorem isClosedEmbedding_topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} :
    IsClosedEmbedding (topEmbR (k := k) (a := a) e (κ := κ)) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  refine ⟨IsEmbedding.of_comp (g := fun x : RankIn k a b {κ} => x.1.submatrix (fun i => e (.inl i)) id)
    (Continuous.subtype_mk (continuous_matrix fun i l => ?_) _)
    (continuous_subtype_val.matrix_submatrix _ _) ?_, ?_⟩
  · obtain ⟨i | i, rfl⟩ := e.surjective i
    · simp only [topR_inl]
      exact continuous_subtype_val.matrix_elem _ _
    · simp only [topR_inr]
      exact continuous_const
  · convert IsEmbedding.subtypeVal (p := fun y : Matrix c a k => y.rank ∈ ({κ} : Set ℕ)) using 1
    funext y
    ext i l
    exact topR_inl e _ i l
  · rw [range_topEmbR]
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_subtype_val.matrix_elem _ _) continuous_const

theorem lAct_topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} (y : RankIn k a c {κ}) (p : parab k (two e)) :
    lAct _ (topEmbR e y) p = topEmbR e (lAct _ y (show GL c k from leviProj k (two e) p false)) := by
  refine Subtype.ext ?_
  rw [lAct_val]
  ext i l
  refine (mul_topR e _ _ i l).trans ?_
  obtain ⟨i | i, rfl⟩ := e.surjective i
  · refine Eq.trans ?_ (topR_inl e _ i l).symm
    rw [lAct_val]
    have : (show GL c k from leviProj k (two e) p false)⁻¹ = leviProj k (two e) p⁻¹ false := by
      rw [map_inv]; rfl
    rw [this]
    rfl
  · refine Eq.trans ?_ (topR_inr e _ i l).symm
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [(mem_parab_two k).1 (inv_mem p.2), zero_mul]

theorem eq_zero_of_vecMul (e : c ⊕ d ≃ b) {κ : ℕ} (hκ : κ = Fintype.card c) (y : RankIn k a c {κ})
    (v : c → k) (h : v ᵥ* y.1 = 0) : v = 0 := by
  refine GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k a c d b e (topR e y.1)ᵀ
    ((rank_transpose _).trans (((rank_topR e y.1).trans y.2).trans hκ)) (fun i j => topR_inr e _ j i) v ?_
  have hs : (topR e y.1)ᵀ.submatrix id (fun i => e (.inl i)) = y.1ᵀ := by
    ext i l; simp
  rw [hs, mulVec_transpose, h]

theorem exists_topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} (hκ : κ = Fintype.card c) (x : RankIn k a b {κ}) :
    ∃ y, ∃ w ∈ KO k b, x = lAct _ (topEmbR e y) w := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank k a c d b e x.1ᵀ ((rank_transpose _).trans (x.2.trans hκ))
  obtain ⟨u, hu⟩ := (isUnit_transpose _).2 g.isUnit
  obtain ⟨p, hp, w, hw, h⟩ := iwasawa_blockTriangular k b (fun i => (blk (two e) i).toNat) u
  have hp' : p ∈ parab k (two e) := (mem_parab_two k).2 fun i j => hp (by
    rw [← two_false e, ← two_true e]; simp only [blk_apply]; simp)
  have : lAct _ x u⁻¹ ∈ Set.range (topEmbR (k := k) (a := a) e (κ := κ)) := by
    rw [range_topEmbR]
    intro j i
    rw [lAct_val, inv_inv, hu, ← transpose_transpose x.1, ← transpose_mul]
    exact hg i j
  obtain ⟨y, hy⟩ := this
  refine ⟨_, w, hw, Eq.trans ?_ (congrArg (lAct _ · w) (lAct_topEmbR e y ⟨p, hp'⟩))⟩
  show x = lAct _ (lAct _ _ p) w
  rw [hy, ← lAct_mul, ← lAct_mul, ← h, inv_mul_cancel, lAct_one]

theorem fibChar_fst (e : c ⊕ d ≃ b) (μ : kˣ →* ℂˣ) (γ : GL a k) :
    fibChar a c d μ (γ, 1, 1) = omChar a b μ (γ, 1) := by
  have hb : ((Fintype.card c : ℂ) + Fintype.card d) / 2 = (Fintype.card b : ℂ) / 2 := by
    rw [← Fintype.card_congr e, Fintype.card_sum]; push_cast; ring
  simp [fibChar, omChar, hb]

theorem fibStr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a b c d : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (κ : ℕ), κ = Fintype.card c → ∀ μ : kˣ →* ℂˣ,
    IsSmoothChar μ → Nonempty ((omegaOn a b μ {κ}).Equiv (indSnd e (fibRep a c d μ κ))) := by
  intro k _ _ _ _ a b c d _ _ _ _ _ _ _ _ e κ hκ μ hμ
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨E, hE⟩ := GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced (GL b k) (RankIn k a b {κ}) (RankIn k a c {κ})
    (SB (RankIn k a c {κ})) (lAct {κ}) (lAct_one _) (lAct_mul _) (continuous_lAct _)
    (topEmbR e) (isClosedEmbedding_topEmbR e) (parab k (two e)) (KO k b) SplitFlip.isCompact_KO
    (exists_topEmbR e hκ)
    (fun y p => lAct _ y (show GL c k from leviProj k (two e) p false)) (lAct_topEmbR e)
    (fun y y' g h => by
      refine inv_mem_iff.1 ((mem_parab_two k).2 fun j i => ?_)
      have h0 : (fun m => (g⁻¹).val (e (.inr j)) (e (.inl m))) ᵥ* y.1 = 0 := by
        funext l
        have := congrArg (fun x : RankIn k a b {κ} => x.1 (e (.inr j)) l) h
        simp only [lAct_val] at this
        exact (mul_topR e _ _ _ l).symm.trans (this.trans (topR_inr e _ j l))
      exact congrFun (eq_zero_of_vecMul e hκ y _ h0) i)
    ((omChar a b μ).comp (MonoidHom.inr _ _))
    ((isSmoothChar_omChar hμ).comp _ (continuous_const.prodMk continuous_id))
    ((twist (MonoidHom.comp ((fibRep a c d μ κ).comp (MonoidHom.inr _ _)) (leviTwo k c d).symm.toMonoidHom)
      (deltaHalf k (Two c d))).comp (leviProj k (two e)))
    (LinearEquiv.refl ℂ _)
    (fun p w y => by
      set m := leviProj k (two e) p with hm
      have hd : GeneralLinearGroup.det (p : GL b k) =
          GeneralLinearGroup.det (m false) * GeneralLinearGroup.det (m true) :=
        (det_parab k (two e) p).trans ((Fintype.prod_bool _).trans (mul_comm _ _))
      have hδ := deltaHalf_two (k := k) (m false, m true)
      rw [show leviTwo k c d (m false, m true) = m from (leviTwo k c d).right_inv m] at hδ
      show (deltaHalf k (Two c d) m : ℂ) * (fibRep a c d μ κ (1, m false, m true) w).1 y = _
      rw [fibRep_apply, ← mul_assoc, ← Units.val_mul]
      refine congrArg₂ _ (congrArg _ ?_) rfl
      rw [hδ]
      simp only [fibChar, omChar, MonoidHom.comp_apply, MonoidHom.mul_apply, detChar_apply,
        MonoidHom.inr_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one, one_mul, hd, map_mul,
        neg_div, absPow_neg, MonoidHom.inv_apply, absPow_add, mul_inv, inv_inv, inv_one]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp)
  have hE' : ∀ Φ g y, ((E Φ).1.1 g).1 y =
      (omChar a b μ (1, g) : ℂ) * Φ.1 (lAct _ (topEmbR e y) g) := hE
  refine ⟨.mk E fun g => LinearMap.ext fun Φ => Subtype.ext (Subtype.ext (funext fun x =>
    Subtype.ext (funext fun y => ?_)))⟩
  obtain ⟨γ, h⟩ := g
  refine (hE' _ x y).trans (Eq.trans ?_ (fibRep_apply a c d μ κ γ 1 1 ((E Φ).1.1 (x * h)) y).symm)
  rw [hE', omegaOn_apply, fibChar_fst e, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul,
    ← map_mul, ← map_mul]
  refine congrArg₂ _ (congrArg _ (congrArg _ (by simp))) (congrArg _ (Subtype.ext ?_))
  simp only [lAct_val, act, topEmbR, Units.val_mul, topR_mul, _root_.mul_inv_rev, Matrix.mul_assoc,
    Units.val_one, Matrix.one_mul, inv_one, Matrix.mul_one]

end GlobalTheory.CompanionTheory.ThetaGLLen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoitouTateEulerCharacteristic
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GaloisCoh

theorem selmer_sha_eq_comap_ker :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), (∀ L : LocCond ρ (locFam S Av), Sel ρ (locFam S Av) (continuous_locFam S Av) L = (Submodule.pi Set.univ L).comap (loc1 S Av ρ)) ∧ Sha1 ρ (locFam S Av) (continuous_locFam S Av) = LinearMap.ker (loc1 S Av ρ) ∧ Sha2 ρ (locFam S Av) (continuous_locFam S Av) = LinearMap.ker (loc2 S Av ρ) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ
  refine ⟨fun L => ?_, ?_, ?_⟩
  · ext x
    simp [mem_Sel, loc1, Submodule.mem_pi]
  · ext x
    simp [Sha1, loc1, Submodule.mem_iInf, LinearMap.mem_ker, funext_iff]
  · ext x
    simp [Sha2, loc2, Submodule.mem_iInf, LinearMap.mem_ker, funext_iff]

end GlobalTheory.CompanionTheory.GaloisCoh

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolyEqPolyEquiv
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.PolyBij
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {n d : ℕ}

theorem cone_empty_nonneg {g : Gam n d} (hg : g ∈ (cone ∅ : AddSubmonoid (Gam n d))) (e : E n d) : 0 ≤ g e := by
  have hg' : (∀ l : Fin n, 0 ≤ g (Sum.inl l)) ∧ (∀ j ∉ (∅ : Finset (Fin d)), 0 ≤ g (Sum.inr j)) ∧
      0 ≤ tdeg g := hg
  rcases e with l | j
  · exact hg'.1 l
  · exact hg'.2.1 j (Finset.notMem_empty j)

theorem coe_mem_cone (f : E n d →₀ ℕ) :
    (fun e => (f e : ℤ) : Gam n d) ∈ (cone ∅ : AddSubmonoid (Gam n d)) := by
  show (∀ l : Fin n, (0 : ℤ) ≤ (f (Sum.inl l) : ℤ)) ∧
    (∀ j ∉ (∅ : Finset (Fin d)), (0 : ℤ) ≤ (f (Sum.inr j) : ℤ)) ∧ 0 ≤ tdeg (fun e => (f e : ℤ) : Gam n d)
  refine ⟨fun l => Int.natCast_nonneg _, fun j _ => Int.natCast_nonneg _, ?_⟩
  exact Finset.sum_nonneg fun j _ => Int.natCast_nonneg _

def expEquiv : (E n d →₀ ℕ) ≃+ (cone ∅ : AddSubmonoid (Gam n d)) where
  toFun f := ⟨fun e => (f e : ℤ), coe_mem_cone f⟩
  invFun g := Finsupp.equivFunOnFinite.symm fun e => (g.1 e).toNat
  left_inv f := by
    ext e
    simp
  right_inv g := by
    refine Subtype.ext (funext fun e => ?_)
    simpa using cone_empty_nonneg g.2 e
  map_add' f f' := by
    refine Subtype.ext (funext fun e => ?_)
    simp

def polyEquiv (K : Type) [Field K] : Bp K n d ≃ₐ[K] R0 K n d (∅ : Finset (Fin d)) :=
  AddMonoidAlgebra.domCongr K K expEquiv

theorem expEquiv_single (e : E n d) :
    (expEquiv (Finsupp.single e 1) : (cone ∅ : AddSubmonoid (Gam n d))) = ⟨oneE e, oneE_mem ∅ e⟩ := by
  refine Subtype.ext (funext fun e' => ?_)
  change ((Finsupp.single e 1 : E n d →₀ ℕ) e' : ℤ) = (Pi.single e (1 : ℤ) : E n d → ℤ) e'
  by_cases h : e' = e
  · subst h
    simp
  · simp [Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]

theorem poly_eq_polyEquiv (K : Type) [Field K] :
    poly n K (∅ : Finset (Fin d)) = (polyEquiv K).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro e
  rw [poly_X, polyEquiv,
    MvPolynomial.X, ← MvPolynomial.single_eq_monomial]
  erw [AddMonoidAlgebra.domCongr_single, expEquiv_single]
  rfl

theorem poly_bijective {K : Type} [Field K] {n d : ℕ} :
    Function.Bijective (poly n K (∅ : Finset (Fin d))) := by
  rw [poly_eq_polyEquiv]
  exact (polyEquiv K).bijective

end GlobalTheory.CompanionTheory.SurjectionOntoH4.PolyBij
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelmerGroupDualExact
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GalDual

theorem contAction_twDual_of_continuous {R Γ M : Type*} [CommRing R] [TopologicalSpace R]
    [DiscreteTopology R] [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [AddCommGroup M]
    [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (χ : Γ →* Rˣ)
    (hχ : Continuous χ) (ρ : Representation R Γ M) (hρ : ContAction ρ) :
    ContAction (twDual χ ρ) := by
  have key : ∀ φ : TDual R M, Continuous (fun g : Γ => twDual χ ρ g φ) := by
    intro φ
    rw [continuous_discrete_rng]
    intro ψ
    have hset : (fun g : Γ => twDual χ ρ g φ) ⁻¹' {ψ} =
        ⋂ m : M, (fun g : Γ => ((χ g : Rˣ) : R) * φ (ρ g⁻¹ m)) ⁻¹' {ψ m} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      exact ⟨fun h m => by rw [← h]; rfl, fun h => TDual.ext h⟩
    rw [hset]
    refine isOpen_iInter_of_finite fun m => ?_
    have h1 : Continuous fun g : Γ => ρ g⁻¹ m :=
      Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) hρ
        (continuous_inv.prodMk continuous_const)
    have h2 : Continuous fun g : Γ => φ (ρ g⁻¹ m) :=
      (continuous_of_discreteTopology (f := fun x : M => φ x)).comp h1
    have h3 : Continuous fun g : Γ => ((χ g : Rˣ) : R) * φ (ρ g⁻¹ m) :=
      (Units.continuous_val.comp hχ).mul h2
    exact (isOpen_discrete {ψ m}).preimage h3
  exact continuous_prod_of_discrete_right.2 key

theorem contAction_twDual : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω)
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ), μ.comp (toGS Ω _) = cycMod F Ω l r → ContAction (twDual μ ρ) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ hμ
  have hc : Continuous μ := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have : (μ ∘ QuotientGroup.mk : G F Ω → _) = cycMod F Ω l r := by rw [← hμ]; rfl
    rw [this]; exact continuous_cycMod
  exact contAction_twDual_of_continuous μ hc ρ hρ

end GlobalTheory.CompanionTheory.GalDual
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitExtensionFundamentalDomain
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem exists_haar_fundamentalDomain : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁), Continuous ι → Continuous π → (∀ u, π (ι u) = u) → ∀ (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ] [Countable Γ₁], (∃ U ∈ 𝓝 (1 : P), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ u ∈ Γ₁, ι u ∈ Γ) → (∀ γ ∈ Γ, π γ ∈ Γ₁) → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁), IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → (∃ K : Set P, IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ Γ, π γ = 1 ∧ γ * m ∈ K) → ∃ (ν : Measure π.ker) (𝓕N : Set π.ker) (μP : Measure P) (𝓕P : Set P), ν.IsHaarMeasure ∧ IsFundamentalDomain (Γ.subgroupOf π.ker) 𝓕N ν ∧ ν 𝓕N ≠ 0 ∧ ν 𝓕N < ⊤ ∧ μP.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕P μP ∧ μP 𝓕P < ⊤ ∧ ∀ f : P → ℝ≥0∞, Measurable f → ∫⁻ p in 𝓕P, f p ∂μP = ∫⁻ u in 𝓕₁, ∫⁻ m in 𝓕N, f ((m : P) * ι u) ∂ν ∂μ₁ := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ _ hU hΓ₁ hΓ μ₁ _ 𝓕₁ h𝓕₁ hfin hK
  have hcl : IsClosed (π.ker : Set P) := by
    have : (π.ker : Set P) = π ⁻¹' {1} := by ext; simp [MonoidHom.mem_ker]
    rw [this]; exact isClosed_singleton.preimage hπ
  haveI : LocallyCompactSpace π.ker := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨D, hDm, hDu, hD⟩ := GlobalTheory.T.parabolic_fundamental_domain_split P G₁ ι π hι hπ hπι Γ hU hK
  let ν : Measure π.ker := Measure.haar
  obtain ⟨hνF, hν0, hνfin⟩ := hD ν
  obtain ⟨δ, hδm, hδΓ, hδ⟩ := GlobalTheory.T.parabolic_haar_decomposition P G₁ ι π hι hπ hπι Γ Γ₁ hΓ₁ ν D hDm hνF hν0 hνfin
  have hδ1 := GlobalTheory.T.modular_character_trivial_finite_covolume G₁ Γ₁ μ₁ 𝓕₁ h𝓕₁ hfin δ hδm hδΓ
  have hmap : ∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = ν := by
    intro u; rw [hδ u, hδ1 u, one_smul]
  have hH := GlobalTheory.T.parabolic_quotient_measure P G₁ ι π hι hπ hπι ν μ₁ hmap
  obtain ⟨hnull, hint⟩ := GlobalTheory.T.parabolic_levi_integral_formula P G₁ ι π hι hπ hπι ν μ₁ D 𝓕₁ hDm h𝓕₁.nullMeasurableSet
  have hcov := GlobalTheory.T.parabolic_fundamental_domain_volume P G₁ ι π hι hπ hπι Γ Γ₁ hΓ₁ ν μ₁ D 𝓕₁ hDu h𝓕₁
  have hdis := GlobalTheory.T.parabolic_integral_unfolding P G₁ ι π hι hπ hπι Γ Γ₁ hΓ ν μ₁ D 𝓕₁ hDu h𝓕₁
  refine ⟨ν, D, _, _, inferInstance, hνF, hν0, hνfin, hH,
    IsFundamentalDomain.mk'' hnull hcov hdis (fun γ => (measurePreserving_smul γ _).quasiMeasurePreserving), ?_, hint⟩
  have h1 := hint (fun _ => 1) measurable_const
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ, setLIntegral_one] at h1
  rw [h1]
  exact ENNReal.mul_lt_top hνfin hfin

end GlobalTheory.CompanionTheory.SplitExtLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateShafarevichDualityH1
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.PoitouTateGlue

theorem range_localization_eq_annihilator (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω)
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ)
    (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
    (h : NineTermExact S Av μ j ρ hρ) :
    LinearMap.range (loc1 S Av ρ) =
      ⨅ y ∈ LinearMap.range (loc1 S Av (twDual μ ρ)), LinearMap.ker (sumPair S Av μ j ρ hρ y) := by
  obtain ⟨δ₁, δ₂, -, -, -, -, hex, -⟩ := h
  have key : ∀ z x, sumPair S Av μ j ρ hρ (loc1 S Av (twDual μ ρ) z) x =
      GlobalTheory.Published.PoitouTate.tr1 S Av μ j ρ hρ x z := by
    intro z x
    simp [sumPair, GlobalTheory.Published.PoitouTate.tr1, loc1, LinearMap.sum_apply]
  ext x
  rw [Submodule.mem_iInf]
  constructor
  · intro hx y
    rw [Submodule.mem_iInf]
    rintro ⟨z, rfl⟩
    rw [LinearMap.mem_ker, key, (hex x).mpr (LinearMap.mem_range.mp hx)]
    simp
  · intro hx
    obtain ⟨y, hy⟩ := (hex x).mp (LinearMap.ext fun z => by
      have hz := (Submodule.mem_iInf _).mp (hx (loc1 S Av (twDual μ ρ) z)) ⟨z, rfl⟩
      rw [LinearMap.mem_ker, key] at hz
      simpa using hz)
    exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.PoitouTateGlue
end

