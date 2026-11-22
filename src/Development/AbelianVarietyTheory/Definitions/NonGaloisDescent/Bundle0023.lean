import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.InfOfIsBaseChange

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolyEqOfIsRowPar
section
noncomputable section

namespace GlobalTheory.EigTie

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.Triple (IsParam IsResidual FbAt)
open GlobalTheory.HeightCounting (RowSide PlSide IotaOk setTy factRes)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)

variable {D : D7}

theorem mem_plB (Pl : PlSide D) (w : D.what₂.places.Pl) (z : Zbar (D.what₂.places.resChar w)) :
    Pl.ι w (z : Qbar (D.what₂.places.resChar w)) ∈ Pl.plB w := by
  rw [Pl.plB_eq, RingEquiv.symm_apply_apply]
  exact z.2

def plRed (Pl : PlSide D) (w : D.what₂.places.Pl) : Zbar (D.what₂.places.resChar w) →+* FbAt D w :=
  ((Pl.plκ w).toRingHom.comp (IsLocalRing.residue (Pl.plB w))).comp
    (((Pl.ι w).toRingHom.comp (Zbar (D.what₂.places.resChar w)).subtype).codRestrict (Pl.plB w) (mem_plB Pl w))

theorem plRed_eq (Pl : PlSide D) (w : D.what₂.places.Pl) (z : Zbar (D.what₂.places.resChar w)) :
    plRed Pl w z = Formalism.L2.NT.redThrough (Pl.plB w) (Pl.plκ w) (Pl.ι w z) := by
  rw [Formalism.L2.NT.redThrough, dif_pos (mem_plB Pl w z)]
  rfl

theorem teichAt_of_iotaOk {Pl : PlSide D} (h : IotaOk D Pl) (w : D.what₂.places.Pl) : TeichAt (Pl.ι w) w (plRed Pl w) :=
  fun k _ v x _ z hz => by rw [plRed_eq, hz, RingEquiv.apply_symm_apply, h]

theorem resTied_of_plSide {Rw : RowSide D} {Pl : PlSide D} (h : IotaOk D Pl)
    (hr : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ σ π r, D.nd.goodRow σ → OnW D σ → IsRowPar Rw σ π →
      IsGaloisRepOf D π _ (Pl.ι w) r → IsSSRep (D.ntypes.rbar σ w) ∧ ∀ g, ∃ p : (Zbar (D.what₂.places.resChar w))[X],
        p.map (Zbar (D.what₂.places.resChar w)).subtype = ((r g : GL (Fin D.R.r) (Qbar (D.what₂.places.resChar w))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.what₂.places.resChar w))).charpoly ∧
        p.map (plRed Pl w) =
          ((D.ntypes.rbar σ w g : GL (Fin D.R.r) (FbAt D w)) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)).charpoly) :
    ResTied D Rw := by
  intro w hw l _ e
  subst e
  exact ⟨Pl.ι w, plRed Pl w, Pl.ι_w w, teichAt_of_iotaOk h w, fun σ π r h1 h2 h3 h4 =>
    ⟨(hr w hw σ π r h1 h2 h3 h4).1, (hr w hw σ π r h1 h2 h3 h4).2, teichAt_of_iotaOk h w⟩⟩

def HasIntForm {Γ : Type} [Group Γ] {l n : ℕ} [Fact l.Prime] (r : Γ →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ A : GL (Fin n) (Qbar l), ∀ g p q, ‖((A⁻¹ * r g * A : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) p q‖ ≤ 1

end GlobalTheory.EigTie

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSmallStable
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open scoped Topology

namespace GlobalTheory.LBC.Model

section Line

variable {G : Type} [Group G]

theorem hasLevelTrace_line (χ : G →* ℂˣ) {K : Subgroup G} (hK : (K : Set G) ⊆ χ.ker) (A : ℂ →ₗ[ℂ] ℂ) (c : ℂ) :
    HasLevelTrace (ofChar χ) K A c ↔ c = A 1 := by
  have hk : ∀ x : K, χ x = 1 := fun x => hK x.2
  have htop : fixed (ofChar χ) K = ⊤ := by
    ext v; simp [fixed, eig, hk]
  have hbot : twKer (ofChar χ) K 1 = ⊥ := by
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨x, v, rfl⟩
    simp [hk]
  have h1 : Module.finrank ℂ (fixed (ofChar χ) K) = 1 := by
    rw [htop, finrank_top, Module.finrank_self]
  have hT : IsLevelProj (ofChar χ) K A (A 1 • LinearMap.id) := fun v => by
    have : A v = (v : ℂ) * A 1 := by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    simp [this, mul_comm]
  have h0 : HasLevelTrace (ofChar χ) K A (A 1) :=
    ⟨inferInstance, _, hT, by simp [h1]⟩
  exact ⟨fun h => h.unique (by simp [hbot]) h0, fun h => h ▸ h0⟩

end Line

section Norm

variable {k k' : Type} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k'] [IsGalois k k']

theorem prod_pow_eq_norm {s : k' ≃ₐ[k] k'} (hs : ∀ t, t ∈ Subgroup.zpowers s) (x : k') :
    ∏ j : Fin (Module.finrank k k'), (s ^ (j : ℕ)) x = algebraMap k k' (Algebra.norm k x) := by
  have ho : orderOf s = Module.finrank k k' := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, IsGalois.card_aut_eq_finrank]
  rw [Algebra.norm_eq_prod_automorphisms]
  refine Fintype.prod_bijective (fun j : Fin (Module.finrank k k') => s ^ (j : ℕ)) ?_ _ _ fun _ => rfl
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun i j h => Fin.ext ?_, ?_⟩
  · exact pow_injOn_Iio_orderOf (by rw [ho]; exact i.2) (by rw [ho]; exact j.2) h
  · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

omit [FiniteDimensional k k'] [IsGalois k k'] in

theorem det_galAct (s : k' ≃ₐ[k] k') {n : ℕ} (g : GL (Fin n) k') :
    (galAct s n g : Matrix (Fin n) (Fin n) k').det = s (g : Matrix (Fin n) (Fin n) k').det :=
  ((s.toAlgHom.toRingHom).map_det (g : Matrix (Fin n) (Fin n) k')).symm

theorem det_norm {s : k' ≃ₐ[k] k'} (hs : ∀ t, t ∈ Subgroup.zpowers s) {n : ℕ} (g : GL (Fin n) k') :
    (norm k s g : Matrix (Fin n) (Fin n) k').det =
      algebraMap k k' (Algebra.norm k (g : Matrix (Fin n) (Fin n) k').det) := by
  rw [← prod_pow_eq_norm hs]
  have h := map_list_prod ((Units.coeHom k').comp (GeneralLinearGroup.det (n := Fin n) (R := k')))
    (List.ofFn fun j : Fin (Module.finrank k k') => galAct (s ^ (j : ℕ)) n g)
  rw [List.map_ofFn, List.prod_ofFn] at h
  refine h.trans (Finset.prod_congr rfl fun j _ => ?_)
  exact det_galAct _ g

theorem det_of_charpoly {s : k' ≃ₐ[k] k'} (hs : ∀ t, t ∈ Subgroup.zpowers s) {n : ℕ} {g : GL (Fin n) k'}
    {γ : GL (Fin n) k} (h : (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k k') =
      (norm k s g : Matrix (Fin n) (Fin n) k').charpoly) :
    GeneralLinearGroup.det γ = Units.map (Algebra.norm k : k' →* k) (GeneralLinearGroup.det g) := by
  ext
  apply (algebraMap k k').injective
  change algebraMap k k' (γ : Matrix (Fin n) (Fin n) k).det =
    algebraMap k k' (Algebra.norm k (g : Matrix (Fin n) (Fin n) k').det)
  rw [← det_norm hs, det_eq_sign_charpoly_coeff, det_eq_sign_charpoly_coeff, ← h]
  simp

end Norm

section Lift

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k']
  [FiniteDimensional k k'] [IsGalois k k']

theorem isLBC_det {s : k' ≃ₐ[k] k'} (hs : ∀ t, t ∈ Subgroup.zpowers s) (n : ℕ) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ)
    (hN : IsSmoothChar (χ.comp (Units.map (Algebra.norm k : k' →* k)))) :
    IsLBC s (detRep (Fin n) χ) (detRep (Fin n) (χ.comp (Units.map (Algebra.norm k : k' →* k)))) := by
  refine ⟨(isSmooth_ofChar_iff _).2 hχ.detChar, isIrreducible_ofChar _, (isSmooth_ofChar_iff _).2 hN.detChar,
    isIrreducible_ofChar _, LinearMap.id, ⟨fun g => ?_, Module.finrank_pos, one_pow _⟩, fun g _ γ h =>
      ⟨χ (GeneralLinearGroup.det γ), ⟨_, hN.detChar.mem_nhds (by simp), fun K _ _ _ hK => ?_⟩,
        ⟨_, hχ.detChar.mem_nhds (by simp), fun K _ _ hK => ?_⟩⟩⟩
  · have : Units.map (Algebra.norm k : k' →* k) (GeneralLinearGroup.det (galAct s n g)) =
        Units.map (Algebra.norm k : k' →* k) (GeneralLinearGroup.det g) := by
      ext
      change Algebra.norm k (galAct s n g : Matrix (Fin n) (Fin n) k').det =
        Algebra.norm k (g : Matrix (Fin n) (Fin n) k').det
      rw [det_galAct, Algebra.norm_eq_of_algEquiv]
    ext
    simp [detRep, this]
  · refine (hasLevelTrace_line _ hK _ _).2 ?_
    simp [detRep, det_of_charpoly hs h]
  · refine (hasLevelTrace_line _ hK _ _).2 ?_
    simp [detRep]

omit [FiniteDimensional k k'] [IsGalois k k'] in

theorem exists_small (n : ℕ) (U : Set (GL (Fin n) k)) (hU : U ∈ 𝓝 (1 : GL (Fin n) k)) :
    ∃ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧
      (K : Set (GL (Fin n) k)) ⊆ U := by
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
  exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

omit [IsGalois k k'] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem exists_small_stable (hc : ∀ t : k' ≃ₐ[k] k', Continuous t) (s : k' ≃ₐ[k] k') (n : ℕ) (U : Set (GL (Fin n) k'))
    (hU : U ∈ 𝓝 (1 : GL (Fin n) k')) :
    ∃ K : Subgroup (GL (Fin n) k'), IsOpen (K : Set (GL (Fin n) k')) ∧ IsCompact (K : Set (GL (Fin n) k')) ∧
      IsStable s K ∧ (K : Set (GL (Fin n) k')) ⊆ U := by
  obtain ⟨J, h1, h2, h3⟩ := exists_small n U hU
  have hcont : ∀ t : k' ≃ₐ[k] k', Continuous (galAct t n) := fun t => by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Units.continuous_val.matrix_map (hc t)
    · simp only [← map_inv]
      exact Units.continuous_coe_inv.matrix_map (hc t)
  have hmul : ∀ (a b : k' ≃ₐ[k] k') g, galAct a n (galAct b n g) = galAct (a * b) n g := fun a b g => by
    rw [galAct_mul]; rfl
  let K : Subgroup (GL (Fin n) k') := ⨅ t : k' ≃ₐ[k] k', J.comap (galAct t n)
  have hmem : ∀ g, g ∈ K ↔ ∀ t : k' ≃ₐ[k] k', galAct t n g ∈ J := fun g => by simp [K, Subgroup.mem_iInf]
  have ho : IsOpen (K : Set (GL (Fin n) k')) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun t => h1.preimage (hcont t)
  have hle : (K : Set (GL (Fin n) k')) ⊆ J := fun g hg => by simpa using (hmem g).1 hg 1
  refine ⟨K, ho, h2.of_isClosed_subset (K.isClosed_of_isOpen ho) hle, ?_, hle.trans h3⟩
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem _).2 fun t => by rw [hmul]; exact (hmem x).1 hx _
  · intro hg
    exact ⟨galAct s⁻¹ n g, (hmem _).2 fun t => by rw [hmul]; exact (hmem g).1 hg _, by rw [hmul]; simp⟩

theorem eq_of_isLBC (hc : ∀ t : k' ≃ₐ[k] k', Continuous t) {s : k' ≃ₐ[k] k'} (hs : ∀ t, t ∈ Subgroup.zpowers s)
    {χ : kˣ →* ℂˣ} {ψ : k'ˣ →* ℂˣ} (h : IsLBC s (detRep (Fin 1) χ) (detRep (Fin 1) ψ)) :
    ψ = χ.comp (Units.map (Algebra.norm k : k' →* k)) := by
  obtain ⟨h1, -, h2, -, I, -, H⟩ := h
  have h1' := (isSmooth_ofChar_iff _).1 h1
  have h2' := (isSmooth_ofChar_iff _).1 h2
  have hdet : ∀ {F : Type} [Field F] (z : Fˣ), GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z :=
    fun z => by ext; simp [GeneralLinearGroup.scalar]
  have hchar : ∀ {F : Type} [Field F] (M : Matrix (Fin 1) (Fin 1) F),
      M.charpoly = Polynomial.X - Polynomial.C M.det := fun M => by
    simp [Matrix.charpoly, Matrix.det_unique]
  have key : ∀ z : k'ˣ, (ψ z : ℂ) * I 1 = χ (Units.map (Algebra.norm k : k' →* k) z) := fun z => by
    obtain ⟨c, ⟨U, hU, hU'⟩, ⟨V, hV, hV'⟩⟩ := H (GeneralLinearGroup.scalar (Fin 1) z)
      (by rw [hchar]; exact Polynomial.separable_X_sub_C)
      (GeneralLinearGroup.scalar (Fin 1) (Units.map (Algebra.norm k : k' →* k) z)) (by
        rw [hchar, hchar, det_norm hs]
        simp [GeneralLinearGroup.scalar])
    obtain ⟨K, a1, a2, a3, a4⟩ := exists_small_stable hc s 1 _ (Filter.inter_mem hU (h2'.mem_nhds (by simp)))
    obtain ⟨L, b1, b2, b4⟩ := exists_small 1 _ (Filter.inter_mem hV (h1'.mem_nhds (by simp)))
    have e1 := (hasLevelTrace_line _ (a4.trans Set.inter_subset_right) _ _).1
      (hU' K a1 a2 a3 (a4.trans Set.inter_subset_left))
    have e2 := (hasLevelTrace_line _ (b4.trans Set.inter_subset_right) _ _).1
      (hV' L b1 b2 (b4.trans Set.inter_subset_left))
    simpa [detRep, hdet] using e1.symm.trans e2
  have hI : I 1 = 1 := by simpa using key 1
  ext z
  simpa [hI] using key z

end Lift

section Trivial

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLBC_absPow_iff (s t : ℝ) :
    IsLBC (1 : k ≃ₐ[k] k) (detRep (Fin 1) (absPow k s)) (detRep (Fin 1) (absPow k t)) ↔ s = t := by
  have h1 : ∀ u : k ≃ₐ[k] k, u = 1 := fun u => Subsingleton.elim _ _
  have hs : ∀ u : k ≃ₐ[k] k, u ∈ Subgroup.zpowers (1 : k ≃ₐ[k] k) := fun u => by rw [h1 u]; exact one_mem _
  have hN : ∀ χ : kˣ →* ℂˣ, χ.comp (Units.map (Algebra.norm k : k →* k)) = χ := fun χ => by
    ext z; simp
  constructor
  · intro h
    have e := eq_of_isLBC (fun u => by rw [h1 u]; exact continuous_id) hs h
    rw [hN] at e
    rw [eq_comm, ← sub_eq_zero, ← absPow_ofReal_eq_one (k := k), Complex.ofReal_sub, sub_eq_add_neg, absPow_add,
      absPow_neg, e, mul_inv_cancel]
  · rintro rfl
    have := isLBC_det hs 1 (isSmoothChar_absPow (k := k) s) (by rw [hN]; exact isSmoothChar_absPow _)
    rwa [hN] at this

end Trivial

section Sides

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k']
  {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] in

theorem pow_eq_norm {s : k' ≃ₐ[k] k'} {P : Representation ℂ (GL (Fin n) k') W} {I : W →ₗ[ℂ] W}
    (hI : IsTwInt k s P I) (g : GL (Fin n) k') : (P g * I) ^ Module.finrank k k' = P (norm k s g) := by
  have h1 : ∀ x, I * P x = P (galAct s n x) * I := fun x => (hI.1 x).symm
  have h2 : ∀ (m : ℕ) x, I ^ m * P x = P (galAct (s ^ m) n x) * I ^ m := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      intro x
      rw [pow_succ, mul_assoc, h1, ← mul_assoc, ih, pow_succ, galAct_mul, mul_assoc]; rfl
  have h3 : ∀ m : ℕ, (P g * I) ^ m = P (List.ofFn fun j : Fin m => galAct (s ^ (j : ℕ)) n g).prod * I ^ m := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih, List.ofFn_succ_last, List.prod_append, map_mul, mul_assoc, ← mul_assoc (I ^ m), h2]
      simp [pow_succ, mul_assoc]
  rw [h3, hI.2.2, mul_one]; rfl

theorem CharVal_unique {π : Representation ℂ (GL (Fin n) k) V} (hπ : IsSmooth π) {γ : GL (Fin n) k} {c c' : ℂ}
    (h : CharVal π γ c) (h' : CharVal π γ c') : c = c' := by
  obtain ⟨U, hU, H⟩ := h
  obtain ⟨U', hU', H'⟩ := h'
  obtain ⟨K, a1, a2, a4⟩ := exists_small n _ (Filter.inter_mem hU hU')
  exact (H K a1 a2 (a4.trans Set.inter_subset_left)).unique (isCompl_fixed_twKer hπ a2).disjoint
    (H' K a1 a2 (a4.trans Set.inter_subset_right))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem TwCharVal_unique [FiniteDimensional k k'] (hc : ∀ t : k' ≃ₐ[k] k', Continuous t) {s : k' ≃ₐ[k] k'}
    {P : Representation ℂ (GL (Fin n) k') W} (hP : IsSmooth P) {I : W →ₗ[ℂ] W} {g : GL (Fin n) k'} {c c' : ℂ}
    (h : TwCharVal k s P I g c) (h' : TwCharVal k s P I g c') : c = c' := by
  obtain ⟨U, hU, H⟩ := h
  obtain ⟨U', hU', H'⟩ := h'
  obtain ⟨K, a1, a2, a3, a4⟩ := exists_small_stable hc s n _ (Filter.inter_mem hU hU')
  exact (H K a1 a2 a3 (a4.trans Set.inter_subset_left)).unique (isCompl_fixed_twKer hP a2).disjoint
    (H' K a1 a2 a3 (a4.trans Set.inter_subset_right))

end Sides

end GlobalTheory.LBC.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDiscreteUOfIsDiscrete
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Formalism.L2.Host Formalism.UG
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.BCWords

section Linear

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a N c : ℕ} {n : Fin c → ℕ}

structure IsDiscreteU (V : Submodule ℂ (Sm E a)) : Prop where
  aut : ∀ φ ∈ V, IsAutForm φ
  central : ∃ s : ℝ, ∀ φ ∈ V, ∀ (t : ℝ) (g : GA E a),
    φ.1 (splitCentre E a t * g) = Complex.exp (Complex.I * s * t) * φ.1 g
  sqInt : ∀ φ ∈ V, letI : MeasurableSpace (GA E a) := borel _
    ∃ (μ : Measure (GA E a)) (𝓕 : Set (GA E a)), μ.IsHaarMeasure ∧ IsFundamentalDomain (latticeGL E a) 𝓕 μ ∧
      ∫⁻ g in 𝓕, ‖φ.1 g‖ₑ ^ 2 ∂μ < ⊤
  stable : IsStable V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V

theorem isDiscreteU_of_isDiscrete {V : Submodule ℂ (Sm E a)} (h : IsDiscrete V) : IsDiscreteU V :=
  ⟨h.aut, ⟨0, fun φ hφ t g => by simpa using (h.sqInt φ hφ).1 t g⟩, fun φ hφ => (h.sqInt φ hφ).2, h.stable, h.ne_bot,
    h.irred⟩

def PairedGL (V V' : Submodule ℂ (Sm E a)) (s : Op E a → Op E a) : Prop :=
  ∃ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) ∧ (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) ∧
    (∀ k (φ φ' : V) (ψ ψ' : V'), φ'.1 = act (.fin k) φ.1 → ψ'.1 = act (s (.fin k)) ψ.1 → B φ' ψ' = B φ ψ) ∧
    (∀ k (φ φ' : V) (ψ ψ' : V'), φ'.1 = act (.cpt k) φ.1 → ψ'.1 = act (s (.cpt k)) ψ.1 → B φ' ψ' = B φ ψ) ∧
    ∀ X (φ φ' : V) (ψ ψ' : V'), φ'.1 = act (.lie X) φ.1 → ψ'.1 = act (s (.lie X)) ψ.1 → B φ' ψ + B φ ψ' = 0

def tensorSp (V : ∀ i, Submodule ℂ (Sm E (n i))) : Submodule ℂ ((∀ i, GA E (n i)) → ℂ) :=
  Submodule.span ℂ {F | ∃ φ : ∀ i, V i, F = fun m => ∏ i, (φ i).1.1 (m i)}

def InInd (h : ∑ i, n i = N) (V : ∀ i, Submodule ℂ (Sm E (n i))) (φ : Sm E N) : Prop :=
  (∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, φ.1 (u * g) = φ.1 g) ∧
    φ ∈ GlobalTheory.PRep.smoothPart (finRep E N) ∧ φ ∈ finVec (cptRep E N) ∧
    ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)),
      (fun m => φ.1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g))) ∈ tensorSp V

theorem inInd_iff (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (φ : Sm E N) :
    InInd h (fun i => (π i).V) φ ↔ φ ∈ indForms h π := Iff.rfl

def InNormInd (h : ∑ i, n i = N) (V : ∀ i, Submodule ℂ (Sm E (n i))) (φ : Sm E N) : Prop :=
  ∃ ν : Fin c → HChar E, (∀ i, (ν i).IsAbsPow ((modExp (fun i => Fin (n i)) i : ℝ) / 2)) ∧
    InInd h (fun i => (V i).map (mulChi (n i) (ν i)).toLinearMap) φ

structure IsInfSubquot (h : ∑ i, n i = N) (V : ∀ i, Submodule ℂ (Sm E (n i))) (W₁ W₂ : Submodule ℂ (Sm E N)) : Prop where
  lt : W₂ < W₁
  mem : ∀ φ ∈ W₁, InNormInd h V φ
  cpt : ∀ k, (∀ φ ∈ W₁, act (.cpt k) φ ∈ W₁) ∧ ∀ φ ∈ W₂, act (.cpt k) φ ∈ W₂
  lie : ∀ X, (∀ φ ∈ W₁, act (.lie X) φ ∈ W₁) ∧ ∀ φ ∈ W₂, act (.lie X) φ ∈ W₂

def QuotHasInfChar (W₁ W₂ : Submodule ℂ (Sm E N)) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = N ∧ ∀ u, ∀ φ ∈ W₁, cap τ u φ - (m.map (u + ·)).prod • φ ∈ W₂

end Linear

def diagGL {n : ℕ} (t : Fin n → ℂˣ) : GL (Fin n) ℂ :=
  ⟨Matrix.diagonal fun i => (t i : ℂ), Matrix.diagonal fun i => ((t i)⁻¹ : ℂˣ), by simp, by simp⟩

def torusParam {n : ℕ} (t : Fin n → ℂˣ) (i : Fin (n / 2)) : ℂˣ :=
  t (Fin.castLE (Nat.div_le_self n 2) i) / t (Fin.castLE (Nat.div_le_self n 2) i).rev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def IsUnramBC (π : Submodule ℂ (UA E n → ℂ)) (w : HeightOneSpectrum (𝓞 E))
    (P : SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
    ∀ t : Fin n → ℂˣ, HasSatAt π w s ϖ q (torusParam t) → ∀ B : Multiset ℂˣ,
      (B.map fun z => (X - C (z : ℂ) : ℂ[X])).prod = (diagGL t * thetaGL n (RingHom.id ℂ) (diagGL t)).val.charpoly →
      GlobalTheory.LFun.HasSatGL w P.ρ B

end GlobalTheory.BCWords

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsProjBot
section
noncomputable section

namespace GlobalTheory.ColumnForm

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def IsProj {X : Type} [AddCommGroup X] (u : Representation ℂ (Multiplicative X) V) (L : AddSubgroup X) (χ : L → ℂ)
    (E : Module.End ℂ V) : Prop :=
  IsAvg u L χ E ∧ ∀ y, (∀ x : L, u (Multiplicative.ofAdd (x : X)) y = χ x • y) → E y = y

theorem isProj_bot {X : Type} [AddCommGroup X] (u : Representation ℂ (Multiplicative X) V) :
    IsProj u ⊥ (fun _ => 1) 1 := ⟨isAvg_bot u, fun _ _ => rfl⟩

end GlobalTheory.ColumnForm

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC

namespace GlobalTheory.BcSpeh

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n c : ℕ}

structure Parts (π : Submodule ℂ (UA E n → ℂ)) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
    (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i)) (m : Fin c → (E →+* ℂ) → Multiset ℂ) : Prop where

  pos : ∀ i, 1 ≤ a i ∧ 1 ≤ d i

  csd : ∀ i, (P i).IsCsd

  loc : ∀ i w, (P i).IsLocComp w (ρ i w)

  inf : ∀ i τ, (P i).HasInfChar τ (m i τ)

  weight : ∀ τ lam, HasWeightAt π τ lam → ∑ i, spehInf (d i) (m i τ) = infOfWeight lam

  distinct : ∀ i j, d i = d j → (⟨a i, CG.mk (P i)⟩ : Σ b, CG E b) = ⟨a j, CG.mk (P j)⟩ → i = j

  inert : ∀ (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → Formalism.UG.IsUnramInv ϖ s q →
    ∀ α, HasSatAt π w s ϖ q α → ∃ S : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ (S i)) ∧
      ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
        (GlobalTheory.LGrp.bcParam n α).map (fun z => (z : ℂ))

def BcSpeh : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ) (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)), Parts π a d h P ρ m ∧
        (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧ GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) ∧
        ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))

def BcString : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ), Parts π a d h P ρ m ∧
        ∀ w, IsSplitAt w → ∃ (τ : LocIrr w n) (s : Fin c → Multiset (GlobalTheory.LocGL.IrrGL (w.adicCompletion E))),
          IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ (∀ i, GlobalTheory.LocGL.HasSupport (ρ i w).ρ (s i)) ∧
          GlobalTheory.LocGL.HasSupport τ.ρ (∑ i, ∑ k : Fin (d i), (s i).map fun y => y.nu (((d i : ℂ) - 1) / 2 - (k : ℕ)))

section Trivial

open GlobalTheory.PRep GlobalTheory.UnitaryBC.Model

example {q : ℕ} (hq : q ≠ 0) :
    ∑ k : Fin 3, ({1} : Multiset ℂˣ).map (fun z : ℂˣ => (z : ℂ) * ((q ^ 2 : ℕ) : ℂ) ^ ((((3 : ℕ) : ℂ) - 1) / 2 - (k : ℕ))) =
      (GlobalTheory.LGrp.bcParam 3 (fun _ => Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ 2)).map fun z : ℂˣ => (z : ℂ) := by
  have e1 : ((((3 : ℕ) : ℂ) - 1) / 2 - ((0 : Fin 3) : ℕ)) = 1 := by norm_num
  have e2 : ((((3 : ℕ) : ℂ) - 1) / 2 - ((1 : Fin 3) : ℕ)) = 0 := by norm_num
  have e3 : ((((3 : ℕ) : ℂ) - 1) / 2 - ((2 : Fin 3) : ℕ)) = -1 := by norm_num
  rw [Fin.sum_univ_three, e1, e2, e3, Complex.cpow_neg, add_right_comm]
  simp [GlobalTheory.LGrp.bcParam]

end Trivial

end GlobalTheory.BcSpeh
end
end

