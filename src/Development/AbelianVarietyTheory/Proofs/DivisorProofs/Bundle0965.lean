import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0952
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeAutomorphismModHalfLevel
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabInduce

section Abstract

variable {R L A : Type} [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup A]

theorem exists_induced (N : Submodule R L) (φ : L →+ A) (s : R → A →+ A) (H C : AddSubgroup A)
    (hφs : ∀ r a, φ (r • a) = s r (φ a)) (hs : ∀ r, ∀ z ∈ C, s r z ∈ C) (hφ : ∀ a, φ a ∈ H)
    (hN : ∀ a, φ a ∈ C ↔ a ∈ N) (hon : ∀ z ∈ H, ∃ a, z - φ a ∈ C)
    (k : A →+ A) (hks : ∀ r z, k (s r z) = s r (k z)) (hkH : ∀ z ∈ H, k z ∈ H) (hkC : ∀ z ∈ C, k z ∈ C) :
    ∃ f : (L ⧸ N) →ₗ[R] (L ⧸ N), ∀ a b, f (N.mkQ a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
  choose g hg using fun a => hon (k (φ a)) (hkH _ (hφ a))
  have key : ∀ a b, N.mkQ (g a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
    intro a b
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hN, map_sub]
    constructor
    · intro h
      have := add_mem (hg a) h
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h (hg a)
      rwa [sub_sub_sub_cancel_left] at this
  let g0 : L →ₗ[R] (L ⧸ N) :=
    { toFun := fun a => N.mkQ (g a)
      map_add' := fun a b => by
        rw [← map_add, key, map_add, map_add, map_add, add_sub_add_comm]
        exact add_mem (hg a) (hg b)
      map_smul' := fun r a => by
        rw [RingHom.id_apply, ← map_smul, key, hφs, hφs, hks, ← map_sub]
        exact hs r _ (hg a) }
  refine ⟨N.liftQ g0 fun a ha => ?_, fun a b => key a b⟩
  change N.mkQ (g a) = 0
  rw [← map_zero N.mkQ, key, map_zero, sub_zero]
  exact hkC _ ((hN a).2 ha)

theorem exists_induced_equiv (N : Submodule R L) (φ : L →+ A) (s : R → A →+ A) (H C : AddSubgroup A)
    (hφs : ∀ r a, φ (r • a) = s r (φ a)) (hs : ∀ r, ∀ z ∈ C, s r z ∈ C) (hφ : ∀ a, φ a ∈ H)
    (hN : ∀ a, φ a ∈ C ↔ a ∈ N) (hon : ∀ z ∈ H, ∃ a, z - φ a ∈ C)
    (k : A →+ A) (hks : ∀ r z, k (s r z) = s r (k z)) (hkH : ∀ z ∈ H, k z ∈ H) (hkC : ∀ z ∈ C, k z ∈ C)
    (k' : A →+ A) (hks' : ∀ r z, k' (s r z) = s r (k' z)) (hkH' : ∀ z ∈ H, k' z ∈ H) (hkC' : ∀ z ∈ C, k' z ∈ C)
    (h1 : ∀ z, k (k' z) = z) (h2 : ∀ z, k' (k z) = z) :
    ∃ γ : (L ⧸ N) ≃ₗ[R] (L ⧸ N), ∀ a b, γ (N.mkQ a) = N.mkQ b ↔ k (φ a) - φ b ∈ C := by
  obtain ⟨f, hf⟩ := exists_induced N φ s H C hφs hs hφ hN hon k hks hkH hkC
  obtain ⟨f', hf'⟩ := exists_induced N φ s H C hφs hs hφ hN hon k' hks' hkH' hkC'
  refine ⟨LinearEquiv.ofLinearMap f f' ?_ ?_, hf⟩
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := N.mkQ_surjective q
    obtain ⟨b, hb⟩ := N.mkQ_surjective (f' (N.mkQ a))
    have h := neg_mem (hkC _ ((hf' a b).1 hb.symm))
    rw [map_sub, h1, neg_sub] at h
    rw [LinearMap.comp_apply, ← hb]
    exact (hf b a).2 h
  · refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := N.mkQ_surjective q
    obtain ⟨b, hb⟩ := N.mkQ_surjective (f (N.mkQ a))
    have h := neg_mem (hkC' _ ((hf a b).1 hb.symm))
    rw [map_sub, h2, neg_sub] at h
    rw [LinearMap.comp_apply, ← hb]
    exact (hf' b a).2 h

end Abstract

section Space

variable {D : D7} (V : HSp D)

noncomputable def halfHom (b : 𝓞 D.host.E) :
    (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddMonoidHom.mk' (halfVec V b) fun _ _ => funext fun _ => mul_add _ _ _

theorem halfVec_eq (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V b z = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • z := rfl

theorem mulVec_halfVec (m : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) (b : 𝓞 D.host.E)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) : m *ᵥ halfVec V b z = halfVec V b (m *ᵥ z) := by
  rw [halfVec_eq, halfVec_eq, Matrix.mulVec_smul]

theorem map_closure_mem (I : Ideal (𝓞 D.host.E))
    (k : (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))
    (hks : ∀ r z, k (halfVec V r z) = halfVec V r (k z)) (hk : ∀ z ∈ latGHat V 1, k z ∈ latGHat V 1) :
    ∀ z ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z},
      k z ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z} := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, z, hz, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨b, hb, k z, hk z hz, hks b z⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

end Space

theorem exists_levGrp_induced : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ κ ∈ GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1, ∃ γ : GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.LevGrp Dw l, ∀ a : Dw.La, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι (liftLa γ a)) ∈ AddSubgroup.closure {u | ∃ b ∈ l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z} := by
  intro D V H Dw l ι hι κ hκ
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hMmem : (l.M : 𝓞 D.host.E) ∈ l.Mb := by
    have h : (l.M : 𝓞 D.host.E) ∈ Ideal.span {(l.M : 𝓞 D.host.E)} := Ideal.mem_span_singleton_self _
    rw [← l.prod] at h
    exact Ideal.mul_le_left h
  have hMb : l.Mb ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hMmem
    exact hM0.ne' (Nat.cast_eq_zero.1 hMmem)
  have hκ1 : ∀ z ∈ latGHat V 1, (finHom V κ).1 *ᵥ z ∈ latGHat V 1 :=
    (GlobalTheory.Member.AALev.congruences_agree D V κ).1.2 hκ.2
  have hκ0 : ∀ z ∈ latHat V, (finHom V κ).1 *ᵥ z ∈ latHat V := by
    intro z hz
    obtain ⟨y, hy, e⟩ := hκ.2 z hz
    rw [one_smul, sub_eq_iff_eq_add] at e
    rw [e]
    exact add_mem hy hz
  have hκ2 : ∀ z ∈ latGHat V 1, (finHom V κ⁻¹).1 *ᵥ z ∈ latGHat V 1 :=
    (GlobalTheory.Member.AALev.congruences_agree D V κ⁻¹).1.2 fun z hz =>
      ⟨_, sub_mem (GlobalTheory.RecDict.finHom_inv_mulVec_mem V κ hκ0 z hz) hz, (one_smul _ _).symm⟩
  let φ : Dw.La →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (fun a => finVec V (ι a)) fun a b => by
      rw [map_add]
      exact GlobalTheory.Member.AALev.fv_add _ _
  have hmem : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  have hsH : ∀ r, ∀ z ∈ latGHat V 1, halfHom V r z ∈ latGHat V 1 := by
    intro r z hz
    rw [hhat] at hz ⊢
    exact GlobalTheory.Member.AALev.hat_smul_int (latG V 1) r hz
  obtain ⟨γ, hγ⟩ := exists_induced_equiv (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) φ (halfHom V) (latGHat V 1)
    (AddSubgroup.closure {u | ∃ b ∈ l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z})
    (fun r a => by
      change finVec V (ι (r • a)) = _
      rw [map_smul]
      exact GlobalTheory.Member.AALev.fv_smul (r : D.host.E) (ι a))
    (fun r => map_closure_mem V l.Mb (halfHom V r) (fun _ _ => funext fun _ => mul_left_comm _ _ _) (hsH r))
    (fun a => by
      rw [hhat]
      exact GlobalTheory.Member.AALev.fv_mem_hat _ (hmem a))
    (fun a => by
      refine (GlobalTheory.T.rationalVector_mem_ideal_completedLattice_iff D V l.Mb hMb (ι a)).trans ?_
      rw [← hι.2, LinearMap.range_eq_map, ← Submodule.map_smul'']
      constructor
      · rintro ⟨x, hx, e⟩
        exact hι.1 e ▸ hx
      · exact fun h => ⟨a, h, rfl⟩)
    (fun z hz => by
      rw [hhat] at hz
      obtain ⟨x, hx, w, hw, e⟩ :=
        (GlobalTheory.AdLat.hat_rational_points_and_approx _ _ _ _ hfg hsp).2.1 l.M hM0 z hz
      rw [← hι.2] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [← hhat] at hw
      refine ⟨a, AddSubgroup.subset_closure ⟨_, hMmem, w, hw, ?_⟩⟩
      rw [e]
      refine (add_sub_cancel_left _ _).trans ?_
      rw [halfVec_eq, ← Nat.cast_smul_eq_nsmul (Af D.host.F ⊗[D.host.F] D.host.E)]
      congr 1
      exact (map_natCast ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F)
        (B := D.host.E)).toRingHom.comp (algebraMap (𝓞 D.host.E) D.host.E)) l.M).symm)
    (Matrix.mulVecLin (finHom V κ).1).toAddMonoidHom (mulVec_halfVec V _) hκ1
    (map_closure_mem V l.Mb _ (mulVec_halfVec V _) hκ1)
    (Matrix.mulVecLin (finHom V κ⁻¹).1).toAddMonoidHom (mulVec_halfVec V _) hκ2
    (map_closure_mem V l.Mb _ (mulVec_halfVec V _) hκ2)
    (fun z => by
      change (finHom V κ).1 *ᵥ ((finHom V κ⁻¹).1 *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, map_inv, Units.mul_inv, Matrix.one_mulVec])
    (fun z => by
      change (finHom V κ⁻¹).1 *ᵥ ((finHom V κ).1 *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec])
  exact ⟨γ, fun a => (hγ a _).1 (liftLa_spec γ a).symm⟩

end GlobalTheory.StabInduce
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelOfMem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.Per GlobalTheory.AdmBr

namespace GlobalTheory.CrysSubRep

variable {l : ℕ} [Fact l.Prime]

def entExt (L : FinExt l) {d a : ℕ} (M : Matrix (Fin d) (Fin a) (Om l)) : FinExt l :=
  ⟨L.1 ⊔ IntermediateField.adjoin ℚ_[l] (Set.range fun p : Fin d × Fin a => M p.1 p.2),
    haveI := L.2
    haveI : FiniteDimensional ℚ_[l]
        (IntermediateField.adjoin ℚ_[l] (Set.range fun p : Fin d × Fin a => M p.1 p.2)) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    IntermediateField.finiteDimensional_sup _ _⟩

theorem le_entExt (L : FinExt l) {d a : ℕ} (M : Matrix (Fin d) (Fin a) (Om l)) :
    L.1 ≤ (entExt L M).1 := le_sup_left

theorem mem_entExt (L : FinExt l) {d a : ℕ} (M : Matrix (Fin d) (Fin a) (Om l)) (i : Fin d) (j : Fin a) :
    M i j ∈ (entExt L M).1 :=
  (le_sup_right : IntermediateField.adjoin ℚ_[l] _ ≤ (entExt L M).1)
    (IntermediateField.subset_adjoin _ _ ⟨(i, j), rfl⟩)

theorem exists_leftInv {K : Type} [Field K] {d a : ℕ} (M : Matrix (Fin d) (Fin a) K)
    (h : Function.Injective M.mulVec) : ∃ N : Matrix (Fin a) (Fin d) K, N * M = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' M)
    (LinearMap.ker_eq_bot.2 (by rw [Matrix.toLin'_apply', Matrix.coe_mulVecLin]; exact h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' M, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem exists_model_of_mem {Γ : Type} [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) (Om l)) (L : FinExt l)
    (hL : ∀ g i j, (r g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) :
    ∃ ρ : Γ →* GL (Fin a) ↥L.1, Formalism.MainNotions.N.mapRep (algebraMap ↥L.1 (Om l)) ρ = r := by
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M : Γ → Matrix (Fin a) (Fin a) ↥L.1 :=
    fun g => Matrix.of fun i j => ⟨(r g : Matrix (Fin a) (Fin a) (Om l)) i j, hL g i j⟩
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L.1 →+* Matrix (Fin a) (Fin a) (Om l)) :=
    fun A B h => Matrix.ext fun i j => f.injective (by simpa using congrFun (congrFun h i) j)
  have hM : ∀ g, f.mapMatrix (M g) = (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => Matrix.ext fun i j => rfl
  let ρ : Γ →* GL (Fin a) ↥L.1 :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hinj (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hinj (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  exact ⟨ρ, MonoidHom.ext fun g => Units.ext (hM g)⟩

end GlobalTheory.CrysSubRep

namespace GlobalTheory.CrysSubRep

theorem isCrysAt_of_sub : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (d a : ℕ) (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℚ_[l])
    (r : ↥Gw →* GL (Fin a) (Om l)),
    IsCrys (P.PD Bw.Kw) (((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp ((Units.coeHom _).comp ρ) : Representation ℚ_[l] ↥(GK Bw.Kw) (Fin d → ℚ_[l])) →
    ∀ M : Matrix (Fin d) (Fin a) (Om l), Function.Injective M.mulVec →
    (∀ g : ↥Gw, ((ρ (Bw.e g) : GL (Fin d) ℚ_[l]) : Matrix (Fin d) (Fin d) ℚ_[l]).map (algebraMap ℚ_[l] (Om l)) * M =
      M * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) →
    GlobalTheory.Pst.IsCrysAt P Bw r := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw d a ρ r hρ M hM hint
  obtain ⟨T⟩ := hT
  let L : FinExt l := entExt Bw.LL M
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M' : Matrix (Fin d) (Fin a) ↥L.1 := Matrix.of fun i j => ⟨M i j, mem_entExt Bw.LL M i j⟩
  have hM' : M'.map f = M := Matrix.ext fun i j => rfl
  have hinjM' : Function.Injective M'.mulVec := by
    intro x y hxy
    have h1 : ∀ v : Fin a → ↥L.1, M.mulVec (fun i => f (v i)) = fun i => f (M'.mulVec v i) :=
      fun v => funext fun i => by rw [← hM']; exact (RingHom.map_mulVec f M' v i).symm
    have h2 := hM (show M.mulVec (fun i => f (x i)) = M.mulVec (fun i => f (y i)) by rw [h1, h1, hxy])
    exact funext fun i => f.injective (congrFun h2 i)
  obtain ⟨N, hN⟩ := exists_leftInv M' hinjM'
  let ρL : ↥(GK Bw.Kw) →* Matrix (Fin d) (Fin d) ↥L.1 :=
    (RingHom.mapMatrix (algebraMap ℚ_[l] ↥L.1)).toMonoidHom.comp ((Units.coeHom _).comp ρ)
  have hmapρ : ∀ g, ((ρ g : GL (Fin d) ℚ_[l]) : Matrix (Fin d) (Fin d) ℚ_[l]).map (algebraMap ℚ_[l] (Om l)) =
      (ρL g).map f := fun g => by
    simp only [ρL, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
      Units.coeHom_apply, Matrix.map_map]
    congr 1
  have hint' : ∀ g, (ρL (Bw.e g)).map f * M'.map f = M'.map f * (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => by
    rw [← hmapρ, hM']; exact hint g
  have hr : ∀ g, (r g : Matrix (Fin a) (Fin a) (Om l)) = (N * ρL (Bw.e g) * M').map f := fun g => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, hint', ← Matrix.mul_assoc, ← Matrix.map_mul, hN,
      Matrix.map_one f (map_zero f) (map_one f), Matrix.one_mul]
  have hmem : ∀ g i j, (r g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := fun g i j => by
    rw [hr g]; exact ((N * ρL (Bw.e g) * M') i j).2
  obtain ⟨r', hr'⟩ := exists_model_of_mem r L hmem
  have hmod : GlobalTheory.Pst.IsModel Bw r L r' := ⟨le_entExt Bw.LL M, hr'⟩
  have hr'g : ∀ g, ((r' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1).map f =
      (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => by
    rw [← hr']; rfl
  have hinjMap : ∀ {m n : ℕ}, Function.Injective (fun X : Matrix (Fin m) (Fin n) ↥L.1 => X.map f) :=
    fun {m n} X Y h => Matrix.ext fun i j => f.injective (congrFun (congrFun h i) j)
  have hintL : ∀ g, ρL (Bw.e g) * M' = M' * (r' g : Matrix (Fin a) (Fin a) ↥L.1) := fun g =>
    hinjMap (by simp only [Matrix.map_mul]; rw [hr'g]; exact hint' g)
  haveI := L.2
  have hcL : IsCrys (P.PD Bw.Kw) (Formalism.MainNotions.N.matRep ρL) :=
    (GlobalTheory.Pst.isCrys_ext_iff (P.PD Bw.Kw) (fun g => ⟨(ρ g : Matrix (Fin d) (Fin d) ℚ_[l]), fun x => rfl, fun x => rfl⟩)).2 hρ
  refine ⟨L, r', hmod, ?_⟩
  refine GlobalTheory.TateDualCrys.isCrys_of_isSubOfSums T Bw.Kw L (ι := Unit) (fun _ => ρL) (fun _ => hcL) (Fin a → ↥L.1)
    (Bw.repE L r') ⟨1, fun _ => (), LinearMap.pi (fun _ => Matrix.toLin' M'), fun x y h => hinjM' (congrFun h 0), ?_⟩
  intro g v
  funext i
  have e1 := hintL (Bw.e.symm g)
  rw [MulEquiv.apply_symm_apply] at e1
  show M'.mulVec ((r' (Bw.e.symm g) : Matrix (Fin a) (Fin a) ↥L.1).mulVec v) = (ρL g).mulVec (M'.mulVec v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1]

end GlobalTheory.CrysSubRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulNormLeOne
section
noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem isOpen_of_padicLattice {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V] [TopologicalSpace V] [IsModuleTopology ℚ_[p] V]
    (A : AddSubgroup V) (hA : ∀ c : ℚ_[p], ‖c‖ ≤ 1 → ∀ v ∈ A, c • v ∈ A)
    (hN : ∀ v : V, ∃ N : ℕ, (p : ℚ_[p]) ^ N • v ∈ A) : IsOpen (A : Set V) := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[p] V
  let b := Module.finBasis ℚ_[p] V
  choose N hN' using fun i => hN (b i)
  set M := ∑ i, N i with hMdef
  have hp1 : ‖(p : ℚ_[p])‖ ≤ 1 := Padic.norm_p_lt_one.le
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hb : ∀ i, (p : ℚ_[p]) ^ M • b i ∈ A := by
    intro i
    have hle : N i ≤ M := Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
    exact hA _ (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1) _ (hN' i)
  have hpos : 0 < ‖(p : ℚ_[p]) ^ M‖ := norm_pos_iff.2 (pow_ne_zero _ hp0)
  let U : Set V := ⋂ i, (fun v => b.coord i v) ⁻¹' Metric.closedBall 0 ‖(p : ℚ_[p]) ^ M‖
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => ?_
    exact (IsUltrametricDist.isOpen_closedBall _ hpos.ne').preimage
      (IsModuleTopology.continuous_of_linearMap (b.coord i))
  have hUA : U ⊆ A := by
    intro v hv
    simp only [U, Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hv
    rw [← b.sum_repr v]
    refine A.sum_mem fun i _ => ?_
    have : b.repr v i • b i = (b.repr v i / (p : ℚ_[p]) ^ M) • ((p : ℚ_[p]) ^ M • b i) := by
      rw [smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ hp0)]
    rw [this]
    refine hA _ ?_ _ (hb i)
    rw [norm_div, div_le_one hpos]
    exact hv i
  have h0 : (0 : V) ∈ U := by
    simp [U, hpos.le]
  exact AddSubgroup.isOpen_of_mem_nhds A (Filter.mem_of_superset (hU.mem_nhds h0) hUA)

end GlobalTheory.LKRes

namespace GlobalTheory.LKRes

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem exists_pow_smul_norm_le_one (z : PadicAlgCl p) : ∃ N : ℕ, ‖(p : ℚ_[p]) ^ N • z‖ ≤ 1 := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hz') (Padic.norm_p_lt_one (p := p))
  refine ⟨N, ?_⟩
  rw [Algebra.smul_def, norm_mul, map_pow, norm_pow, PadicAlgCl.norm_extends]
  calc ‖(p : ℚ_[p])‖ ^ N * ‖z‖ ≤ ‖z‖⁻¹ * ‖z‖ := by gcongr
    _ = 1 := inv_mul_cancel₀ hz'.ne'

theorem algebraMap_mem_intKQ (r : ℕ) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) :
    algebraMap ℚ_[p] (KQ p K r) c ∈ intKQ p K r := by
  have hK : algebraMap ℚ_[p] K c ∈ GlobalTheory.LKLoc.intK p K := by
    show algebraMap K (PadicAlgCl p) (algebraMap ℚ_[p] K c) ∈ Obar p
    rw [← IsScalarTower.algebraMap_apply, mem_Obar_iff]
    exact (PadicAlgCl.norm_extends (p := p) c).le.trans hc
  exact Subring.subset_closure (Or.inl ⟨⟨_, hK⟩, rfl⟩)

theorem smul_mem_intKQ (r : ℕ) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) (v : KQ p K r) (hv : v ∈ intKQ p K r) :
    c • v ∈ intKQ p K r := by
  rw [Algebra.smul_def]
  exact mul_mem (algebraMap_mem_intKQ p K r c hc) hv

theorem exists_pow_smul_mem_intKQ (r : ℕ) (v : KQ p K r) :
    ∃ N : ℕ, (p : ℚ_[p]) ^ N • v ∈ intKQ p K r := by
  have hp1 : ∀ k : ℕ, ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le
  induction (v : K ⊗[ℚ_[p]] Qr p r) using TensorProduct.induction_on with
  | zero => exact ⟨0, by show (p : ℚ_[p]) ^ 0 • (0 : KQ p K r) ∈ intKQ p K r; rw [smul_zero]; exact zero_mem _⟩
  | tmul x y =>
    obtain ⟨N₁, h₁⟩ := exists_pow_smul_norm_le_one p (x : PadicAlgCl p)
    obtain ⟨N₂, h₂⟩ := exists_pow_smul_norm_le_one p (y : PadicAlgCl p)
    have hx : (p : ℚ_[p]) ^ N₁ • x ∈ GlobalTheory.LKLoc.intK p K := by
      show (((p : ℚ_[p]) ^ N₁ • x : K) : PadicAlgCl p) ∈ Obar p
      rw [IntermediateField.coe_smul, mem_Obar_iff]; exact h₁
    have hy : (p : ℚ_[p]) ^ N₂ • y ∈ GlobalTheory.LKLoc.intR p (Q0 p) r := by
      show (((p : ℚ_[p]) ^ N₂ • y : Qr p r) : PadicAlgCl p) ∈ Obar p
      rw [IntermediateField.coe_smul, mem_Obar_iff]; exact h₂
    refine ⟨N₁ + N₂, ?_⟩
    have key : ((p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y) : K ⊗[ℚ_[p]] Qr p r) =
        (((p : ℚ_[p]) ^ N₁ • x) ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] ((p : ℚ_[p]) ^ N₂ • y)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.smul_tmul_smul, pow_add]
    have e : (p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y : KQ p K r) =
        inclK p K r ((p : ℚ_[p]) ^ N₁ • x) * inclQ p K r ((p : ℚ_[p]) ^ N₂ • y) := key
    show (p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y : KQ p K r) ∈ intKQ p K r
    rw [e]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, hx⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨_, hy⟩, rfl⟩))
  | add a b ha hb =>
    obtain ⟨N₁, h₁⟩ := ha
    obtain ⟨N₂, h₂⟩ := hb
    refine ⟨N₁ + N₂, ?_⟩
    have e : (p : ℚ_[p]) ^ (N₁ + N₂) • (a + b) =
        (p : ℚ_[p]) ^ N₂ • ((p : ℚ_[p]) ^ N₁ • a) + (p : ℚ_[p]) ^ N₁ • ((p : ℚ_[p]) ^ N₂ • b) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm N₂ N₁]
    show (p : ℚ_[p]) ^ (N₁ + N₂) • (a + b : KQ p K r) ∈ intKQ p K r
    rw [e]
    exact add_mem (smul_mem_intKQ p K r _ (hp1 _) _ h₁) (smul_mem_intKQ p K r _ (hp1 _) _ h₂)

end GlobalTheory.LKRes

namespace GlobalTheory.LKRes

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem isOpen_intKQ (hK : FiniteDimensional ℚ_[p] K) (r : ℕ) (hr : 0 < r) :
    IsOpen (intKQ p K r : Set (KQ p K r)) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p r) := finiteDimensional_Kn p (Q0 p) inferInstance hr
  haveI : FiniteDimensional ℚ_[p] (KQ p K r) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))
  haveI : IsModuleTopology ℚ_[p] (KQ p K r) := ⟨rfl⟩
  exact isOpen_of_padicLattice (intKQ p K r).toAddSubgroup
    (fun c hc v hv => smul_mem_intKQ p K r c hc v hv) (exists_pow_smul_mem_intKQ p K r)

theorem mem_Kres_iff (n r : ℕ) (g : GL (Fin n) (KQ p K r)) :
    g ∈ Kres p K n r ↔ ∀ i j, (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r ∧
      ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r := by
  constructor
  · rintro ⟨h, rfl⟩ i j
    exact ⟨((h : Matrix (Fin n) (Fin n) (intKQ p K r)) i j).2,
      (((h⁻¹ : GL (Fin n) (intKQ p K r)) : Matrix (Fin n) (Fin n) (intKQ p K r)) i j).2⟩
  · intro H
    let A : Matrix (Fin n) (Fin n) (intKQ p K r) := Matrix.of fun i j => ⟨_, (H i j).1⟩
    let B : Matrix (Fin n) (Fin n) (intKQ p K r) := Matrix.of fun i j => ⟨_, (H i j).2⟩
    have hA : A.map (intKQ p K r).subtype = (g : Matrix (Fin n) (Fin n) (KQ p K r)) := by ext i j; rfl
    have hB : B.map (intKQ p K r).subtype =
        ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) := by ext i j; rfl
    have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) (intKQ p K r) => M.map (intKQ p K r).subtype :=
      Matrix.map_injective Subtype.val_injective
    have h1 : A * B = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hB]
      exact Units.mul_inv g)
    have h2 : B * A = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hB]
      exact Units.inv_mul g)
    exact ⟨⟨A, B, h1, h2⟩, Units.ext hA⟩

theorem isOpen_Kres : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → IsOpen (Kres p K n r : Set (GL (Fin n) (KQ p K r))) := by
  intro p _ K hK n r hr
  have hS := isOpen_intKQ p K hK r hr
  have e : (Kres p K n r : Set (GL (Fin n) (KQ p K r))) = ⋂ i, ⋂ j,
      ((fun g : GL (Fin n) (KQ p K r) => (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j) ⁻¹' (intKQ p K r : Set _) ∩
       (fun g : GL (Fin n) (KQ p K r) =>
          ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j) ⁻¹' (intKQ p K r : Set _)) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
    exact mem_Kres_iff p K n r g
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (hS.preimage (Units.continuous_val.matrix_elem i j)).inter
    (hS.preimage (Units.continuous_coe_inv.matrix_elem i j))

end GlobalTheory.LKRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalMatrixCoefficientSpanStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_matrixCoefficientSpan : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W), FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  first | exact @GlobalTheory.Proof.CoeffSpan.finiteDimensional_coeffSpan | exact GlobalTheory.Proof.CoeffSpan.finiteDimensional_coeffSpan | (intros; apply GlobalTheory.Proof.CoeffSpan.finiteDimensional_coeffSpan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFieldCharacterLabelsCompatNormPowInvStatement
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (N : ℕ), 0 < N → (∀ (d : ℕ) (h : d ∣ N) (θ : Tor p d →* ℂˣ) (x : Fbar p) (n : ℕ), LabelsChar L θ x → LabelsChar L ((θ.comp (torNorm p h)) ^ n) (x ^ n)) ∧ ∀ (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ), LabelsTame L χ a → LabelsChar L (χ.comp (baseNorm p N)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) ∧ LabelsTame L χ⁻¹ a⁻¹ := by
  first | exact @GlobalTheory.LabelNorm.main | exact GlobalTheory.LabelNorm.main | (intros; apply GlobalTheory.LabelNorm.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDetPowDepthLeOfIntegralLogHomStatement
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupDetPowDepth_le_of_integralLogHom : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (i d d' k : ℕ) (G : LogFGL v d) (G' : LogFGL v d') (φ : Fin d' → MvPowerSeries (Fin d) C) (M : Matrix (Fin d') (Fin d) C), IsIntHom G G' φ M → ∀ u : Fin i → Fin d → C, detDepth G u k ≤ detDepth G' (fun a => M.mulVec (u a)) k := by
  first | exact @GlobalTheory.DepthMono.detDepth_le_of_isIntHom | exact GlobalTheory.DepthMono.detDepth_le_of_isIntHom | (intros; apply GlobalTheory.DepthMono.detDepth_le_of_isIntHom <;> assumption)
end

