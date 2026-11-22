import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.TwOrbConj

variable {G : Type} [Group G]

theorem mem_rStab {H : Type} [Group H] (u : H → ℂ) (k : H) : k ∈ GlobalTheory.BCT.rStab u ↔ ∀ x, u (x * k) = u x := Iff.rfl

theorem mem_twCent (θ : G →* G) (δ x : G) : x ∈ GlobalTheory.BCT.twCent θ δ ↔ x * δ = δ * θ x := Iff.rfl

theorem relIndex_map_equiv (φ : G ≃* G) (H L : Subgroup G) :
    (H.map φ.toMonoidHom).relIndex (L.map φ.toMonoidHom) = H.relIndex L := by
  first
  | (rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.relIndex_comap, Subgroup.map_map]; simp)
  | exact Subgroup.relIndex_map_map_of_injective _ _ φ.injective
  | simp [Subgroup.relIndex]

theorem avg_left {H : Type} [Group H] (u : H → ℂ) (a : H) :
    GlobalTheory.BCT.avg (fun h => u (a * h)) = GlobalTheory.BCT.avg u := by
  have hR : GlobalTheory.BCT.rStab (fun h => u (a * h)) = GlobalTheory.BCT.rStab u := by
    ext k
    rw [mem_rStab, mem_rStab]
    constructor
    · intro h x
      simpa [mul_assoc] using h (a⁻¹ * x)
    · intro h x
      simpa [mul_assoc] using h (a * x)
  unfold GlobalTheory.BCT.avg
  rw [hR]
  congr 1
  have hc : ∀ q : H ⧸ GlobalTheory.BCT.rStab u, u (a * q.out) = u (a • q).out := by
    intro q
    obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul (GlobalTheory.BCT.rStab u) (a * q.out)
    have hq : (a • q) = (QuotientGroup.mk (a * q.out) : H ⧸ GlobalTheory.BCT.rStab u) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hr]
    exact ((mem_rStab u r).1 r.2 (a * q.out)).symm
  simp_rw [hc]
  exact finsum_comp_equiv (f := fun q : H ⧸ GlobalTheory.BCT.rStab u => u q.out) (MulAction.toPerm a)

theorem map_conj_self (H : Subgroup G) {h : G} (hh : h ∈ H) :
    H.map (MulAut.conj h).toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh

theorem map_conj_mul (L : Subgroup G) (a b : G) :
    L.map (MulAut.conj (a * b)).toMonoidHom = (L.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem twCent_conj (θ : G →* G) (δ g : G) :
    GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g) = (GlobalTheory.BCT.twCent θ δ).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have e : (MulAut.conj g⁻¹).symm x = g * x * g⁻¹ := by simp [MulAut.conj_symm_apply]
  rw [e, mem_twCent, mem_twCent, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc g * x * g⁻¹ * δ = g * (x * (g⁻¹ * δ * θ g)) * (θ g)⁻¹ := by group
      _ = g * (g⁻¹ * δ * θ g * θ x) * (θ g)⁻¹ := by rw [h]
      _ = δ * (θ g * θ x * (θ g)⁻¹) := by group
  · intro h
    calc x * (g⁻¹ * δ * θ g) = g⁻¹ * (g * x * g⁻¹ * δ) * θ g := by group
      _ = g⁻¹ * (δ * (θ g * θ x * (θ g)⁻¹)) * θ g := by rw [h]
      _ = g⁻¹ * δ * θ g * θ x := by group

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem cptPart_map (c : G) (T : Subgroup G) :
    GlobalTheory.BCT.cptPart (T.map (MulAut.conj c).toMonoidHom) = (GlobalTheory.BCT.cptPart T).map (MulAut.conj c).toMonoidHom := by
  unfold GlobalTheory.BCT.cptPart
  rw [MonoidHom.map_closure]
  congr 1
  let h : G ≃ₜ G := (Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹)
  have hh : ∀ x, h x = (MulAut.conj c).toMonoidHom x := fun x => by
    simp [h, MulAut.conj_apply]
  have hz : ∀ t, (Subgroup.zpowers ((MulAut.conj c).toMonoidHom t) : Set G) = h '' (Subgroup.zpowers t : Set G) := by
    intro t
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
    ext y
    simp only [Set.mem_image, hh]
  have hk : ∀ t, IsCompact (closure (Subgroup.zpowers ((MulAut.conj c).toMonoidHom t) : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers t : Set G)) := by
    intro t
    rw [hz, ← Homeomorph.image_closure, Homeomorph.isCompact_image]
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (hk t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (hk t).2 hc⟩

theorem relIndex_conj (c : G) (T T' L L' : Subgroup G) (hT : T' = T.map (MulAut.conj c).toMonoidHom)
    (hL : L' = L.map (MulAut.conj c).toMonoidHom) :
    (T' ⊓ L').relIndex (GlobalTheory.BCT.cptPart T') = (T ⊓ L).relIndex (GlobalTheory.BCT.cptPart T) := by
  subst hT hL
  rw [← Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, cptPart_map, relIndex_map_equiv]

def summand (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) : ℂ :=
  (((GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℕ) : ℂ) *
    GlobalTheory.BCT.avg fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))

theorem twOrb_eq (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) :
    GlobalTheory.BCT.twOrb θ K δ f = ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
      summand θ K δ f (Quotient.out q) := rfl

theorem summand_rep (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) {t k : G}
    (ht : t ∈ GlobalTheory.BCT.twCent θ δ) (hk : k ∈ K) : summand θ K δ f (t * y * k) = summand θ K δ f y := by
  unfold summand
  congr 1
  · exact congrArg (fun n : ℕ => (n : ℂ)) (relIndex_conj t _ _ _ _ (map_conj_self _ ht).symm
      (by rw [map_conj_mul, map_conj_mul, map_conj_self K hk]))
  · have hd : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← (mem_twCent θ δ t).1 ht, inv_mul_cancel_left]
    have hfun : (fun k' : K => f ((t * y * k * k')⁻¹ * δ * θ (t * y * k * k'))) =
        fun k' : K => (fun k'' : K => f ((y * k'')⁻¹ * δ * θ (y * k''))) (⟨k, hk⟩ * k') := by
      funext k'
      congr 1
      simp only [Subgroup.coe_mul]
      calc (t * y * k * ↑k')⁻¹ * δ * θ (t * y * k * ↑k')
          = (y * (k * ↑k'))⁻¹ * (t⁻¹ * δ * θ t) * θ (y * (k * ↑k')) := by
            simp only [map_mul, _root_.mul_inv_rev]; group
        _ = (y * (k * ↑k'))⁻¹ * δ * θ (y * (k * ↑k')) := by rw [hd]
    rw [hfun]
    exact avg_left (fun k'' : K => f ((y * k'')⁻¹ * δ * θ (y * k''))) ⟨k, hk⟩

theorem summand_twist (θ : G →* G) (K : Subgroup G) (δ g : G) (f : G → ℂ) (x : G) :
    summand θ K (g⁻¹ * δ * θ g) f x = summand θ K δ f (g * x) := by
  unfold summand
  congr 1
  · exact congrArg (fun n : ℕ => (n : ℂ)) (relIndex_conj g⁻¹ _ _ _ _ (twCent_conj θ δ g)
      (by rw [← map_conj_mul, inv_mul_cancel_left]))
  · congr 1
    funext k
    congr 1
    simp only [map_mul, _root_.mul_inv_rev]
    group

def dcEquiv (θ : G →* G) (K : Subgroup G) (δ g : G) :
    DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g) : Set G) (K : Set G) ≃
      DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) where
  toFun q := DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)
  invFun q := DoubleCoset.mk (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K (g⁻¹ * Quotient.out q)
  left_inv q := by
    obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1
      (DoubleCoset.out_eq' (GlobalTheory.BCT.twCent θ δ) K (DoubleCoset.mk _ K (g * Quotient.out q))).symm
    show DoubleCoset.mk _ K (g⁻¹ * Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q))) = q
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K q]
    rw [DoubleCoset.eq]
    refine ⟨g⁻¹ * t⁻¹ * g, ?_, k⁻¹, K.inv_mem hk, by group⟩
    rw [twCent_conj]
    exact ⟨t⁻¹, (GlobalTheory.BCT.twCent θ δ).inv_mem ht, by simp [MulAut.conj_apply]⟩
  right_inv q := by
    obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1
      (DoubleCoset.out_eq' (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K (DoubleCoset.mk _ K (g⁻¹ * Quotient.out q))).symm
    show DoubleCoset.mk _ K (g * Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K
      (g⁻¹ * Quotient.out q))) = q
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' (GlobalTheory.BCT.twCent θ δ) K q]
    rw [DoubleCoset.eq]
    rw [twCent_conj] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    refine ⟨s⁻¹, (GlobalTheory.BCT.twCent θ δ).inv_mem hs, k⁻¹, K.inv_mem hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end GlobalTheory.TwOrbConj

namespace GlobalTheory.TwOrbConj

theorem twOrb_twConj : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G)
    (δ g : G) (f : G → ℂ), (∀ x : G, (GlobalTheory.BCT.rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) →
    GlobalTheory.BCT.twOrb θ K (g⁻¹ * δ * θ g) f = GlobalTheory.BCT.twOrb θ K δ f := by
  intro G _ _ _ θ K δ g f _
  rw [twOrb_eq, twOrb_eq]
  calc ∑ᶠ q, summand θ K (g⁻¹ * δ * θ g) f (Quotient.out q)
      = ∑ᶠ q, summand θ K δ f (Quotient.out (dcEquiv θ K δ g q)) := by
        refine finsum_congr fun q => ?_
        rw [summand_twist]
        obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1
          (DoubleCoset.out_eq' (GlobalTheory.BCT.twCent θ δ) K (DoubleCoset.mk _ K (g * Quotient.out q))).symm
        show _ = summand θ K δ f (Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)))
        rw [he, summand_rep θ K δ f _ ht hk]
    _ = ∑ᶠ q, summand θ K δ f (Quotient.out q) :=
        finsum_comp_equiv (f := fun q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) =>
          summand θ K δ f (Quotient.out q)) (dcEquiv θ K δ g)

end GlobalTheory.TwOrbConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointEqRealMulFiniteBothOrdersStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (p : GAF σ J), ∃ a ∈ GlobalTheory.WeilPartsF.GinfCF σ J, ∃ k ∈ GlobalTheory.WeilPartsF.GfCF σ J, p = a * k ∧ p = k * a := by
  first | exact @GlobalTheory.WeilPartsF.exists_real_finite_mul | exact GlobalTheory.WeilPartsF.exists_real_finite_mul | (intros; apply GlobalTheory.WeilPartsF.exists_real_finite_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMassLowerBoundOfOrthonormalLatticeFrames
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.StdMass

variable {D : D7}

theorem coord_isIntegral (V : HSp D) (hL : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame))
    {x : Fin V.rank → D.host.E} (hx : x ∈ L0c D V) (k : Fin V.rank) : IsIntegral ℤ (x k) := by
  have key : ∀ y ∈ V.L0, ∃ a : 𝓞 D.host.E, (a : D.host.E) = V.frame.repr y k := by
    intro y hy
    rw [hL] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      by_cases h : j = k
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [Finsupp.single_apply, h]⟩
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hz
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul r y _ hy =>
      obtain ⟨a, ha⟩ := hy
      refine ⟨r * a, ?_⟩
      rw [← algebraMap_smul D.host.E r y, map_smul]
      simp [ha, Algebra.smul_def]
  have hx' : ∑ i, x i • V.frame i ∈ V.L0 := hx
  obtain ⟨a, ha⟩ := key _ hx'
  have e : V.frame.repr (∑ i, x i • V.frame i) k = x k := by
    rw [← Module.Basis.equivFun_symm_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [← e, ← ha]
  exact RingOfIntegers.isIntegral_coe a

theorem mem_lattice_of_rational_mem_completion (V : HSp D) (v : Fin V.rank → D.host.E)
    (h : (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] v k) ∈ latHat D.host.F D.host.E (L0c D V)) : v ∈ L0c D V := by
  let f := V.frame.equivFun.toLinearMap
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (f.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hw
      refine ⟨V.frame.equivFun.symm w, ?_, V.frame.equivFun.apply_symm_apply w⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hw
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective w
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [V.standardTuple_isLattice.span_eq_top]; trivial
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [Submodule.map_span] at this
    exact this
  have hr := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank L (V.standardTuple_isLattice.fg.map _) hsp).1 v
  rw [← hL]
  refine hr.1 ?_
  have hle : latHat D.host.F D.host.E (L0c D V) ≤ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [← hL] at hx
    exact AddSubgroup.subset_closure ⟨a, fun w => ha w, x, hx, rfl⟩
  exact hle h

theorem card_stab_le (V : HSp D) (hg : V.gram = 1)
    (hL : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame)) :
    Nat.card (Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1) ≤ NumberField.Units.torsionOrder D.host.E ^ V.rank * V.rank.factorial := by
  obtain ⟨hSf, hSc⟩ := GlobalTheory.T.integral_unitary_matrices_finite_card_le D V.rank
  have hx : ∀ x : Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1, ∃ u : GL (Fin V.rank) D.host.E,
        u ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram ∧
        Formalism.UG.bc (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) u =
          HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1 := fun x => by
    obtain ⟨u, hu, e⟩ := Subgroup.mem_map.1 x.1.2
    exact ⟨u, hu, e⟩
  choose u hu hue using hx
  have hunit : ∀ x, (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E)ᴴ * (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 :=
    fun x => by
    have h := hu x
    change Formalism.UG.cT _ (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram at h
    rw [hg, Matrix.mul_one] at h
    convert h using 2
    ext a b
    rfl
  have hint : ∀ x a b, IsIntegral ℤ ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := fun x a b => by
    have hK : x.1.1 ∈ GlobalTheory.Mass.Levels.latStab V := by
      have := x.2
      simpa [Formalism.UG.stabAt] using this
    have hej : (Pi.single b 1 : Fin V.rank → D.host.E) ∈ L0c D V := by
      show ∑ i, (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) i • V.frame i ∈ V.L0
      rw [Finset.sum_eq_single b (fun c _ hc => by simp [hc]) (by simp), hL]
      rw [Pi.single_eq_same, one_smul]
      exact Submodule.subset_span ⟨b, rfl⟩
    have hy : (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) k) ∈
        latHat D.host.F D.host.E (L0c D V) :=
      AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, _, hej, rfl⟩
    have h2 := ((GlobalTheory.Mass.Levels.mem_latStab V x.1.1).1 hK _).1 hy
    have e : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1).1 *ᵥ
        (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) k) =
        fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) k b := by
      rw [← hue x]
      funext k
      change ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) *ᵥ
        ((inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) ∘ (Pi.single b 1))) k =
          (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) k b)
      rw [← RingHom.map_mulVec]
      simp [Matrix.mulVec_single_one]
    rw [e] at h2
    exact coord_isIntegral V hL (mem_lattice_of_rational_mem_completion V _ h2) a
  let f : Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1 →
      {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
    fun x => ⟨(u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E), hunit x, hint x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = u y := congrArg Subtype.val hxy
    have h2 : u x = u y := Units.ext h1
    have h3 : HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1 =
        HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram y.1.1 := by
      rw [← hue x, ← hue y, h2]
    have h4 : x.1.1 = y.1.1 := Subtype.ext h3
    exact Subtype.ext (Subtype.ext h4)
  haveI := hSf.to_subtype
  calc Nat.card _ ≤ Nat.card {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
        Nat.card_le_card_of_injective f hf
    _ = Set.ncard {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
        Nat.card_coe_set_eq _
    _ ≤ _ := hSc

theorem massLower_of_stdV : ∀ D : D7, StdV D → MassLower D := by
  intro D hS i _
  obtain ⟨h1, h2⟩ := hS i
  have hg : (Vc D i).gram = 1 := Matrix.ext fun a b => by
    rw [Matrix.one_apply]
    exact h1 a b
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have e : gramAt D (Vc D i) τ = 1 := Matrix.ext fun a b => by
      simp [gramAt, hg, Matrix.one_apply]
    rw [e]
    exact Matrix.PosDef.one
  have hK := GlobalTheory.Mass.Levels.latStab_compact_open (Vc D i)
  have hfc := GlobalTheory.Mass.finiteClasses_unitary (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND (Vc D i)) (GlobalTheory.DefiniteQuotient.isTotDef_of_posDef (Vc D i) hpd) hK.1 hK.2
  have hle := hfc.inv_card_le 1
  have hpos := hfc.stabOrder_pos (DoubleCoset.mk _ _ 1)
  rw [GlobalTheory.Mass.stabOrder_mk] at hpos
  have hc := card_stab_le (Vc D i) hg h2
  have hr : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  unfold GlobalTheory.Mass.unitaryMass
  refine le_trans ?_ hle
  rw [one_div, ← hr]
  exact inv_anti₀ (by exact_mod_cast hpos) (by exact_mod_cast hc)

end GlobalTheory.LowRow.StdMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRealPointsFixFiniteAdelicHoms
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section
namespace GlobalTheory.RealWeilFinFix

theorem actOF_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (g : GAF σ JS) (h : GAF σ JT),
      g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS → h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT → ∀ u : WOF F E nS nT, u.map (infPartF F E) = 0 →
        actOF σ JS JT g h u = u := by
  intro F E _ _ _ _ _ σ nS nT JS JT g h hg hh u hu
  have h1 : (mtF σ JT h).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hh)
  have h2 : (mtF σ JS g⁻¹).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 (inv_mem hg))
  have h3 : (actOF σ JS JT g h u).map (finPartF F E) = u.map (finPartF F E) := by
    unfold actOF
    rw [Matrix.map_mul, Matrix.map_mul, h1, h2, Matrix.one_mul, Matrix.mul_one]
  have h4 : (actOF σ JS JT g h u).map (infPartF F E) = u.map (infPartF F E) := by
    unfold actOF
    rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]
  ext i j
  have k3 : finPartF F E (actOF σ JS JT g h u i j) = finPartF F E (u i j) := congrFun (congrFun h3 i) j
  have k4 : infPartF F E (actOF σ JS JT g h u i j) = infPartF F E (u i j) := congrFun (congrFun h4 i) j
  rw [← Formalism.L2.Fam.ThC.pairE_eta (actOF σ JS JT g h u i j), ← Formalism.L2.Fam.ThC.pairE_eta (u i j)]
  exact congrArg₂ Formalism.L2.Fam.ThC.pairE k4 k3

end GlobalTheory.RealWeilFinFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachModuleMapMatrixCompMul
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachPlace

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}

theorem wachMap_comp_coeff (W : LocWach PD LL O v f) {T T' T'' : LocLat G Qp LL O} {n n' n'' : ℕ}
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (b' : Module.Basis (Fin n') (LetA O f) ↥(W.N T'))
    (b'' : Module.Basis (Fin n'') (LetA O f) ↥(W.N T''))
    (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L)
    (a : Fin n → Fin n' → LetA O f) (a' : Fin n' → Fin n'' → LetA O f) (a'' : Fin n → Fin n'' → LetA O f)
    (h1 : ∀ k, W.map g (b k : W.DD T) = ∑ m, a k m • (b' m : W.DD T'))
    (h2 : ∀ k, W.map g' (b' k : W.DD T') = ∑ m, a' k m • (b'' m : W.DD T''))
    (h3 : ∀ k, W.map g'' (b k : W.DD T) = ∑ m, a'' k m • (b'' m : W.DD T''))
    (hc : ∀ x, g''.f x = g'.f (g.f x)) (k : Fin n) (p : Fin n'') :
    a'' k p = ∑ m, a k m * a' m p := by
  have hg : g'' = latComp g' g := by
    cases g''
    simp only [latComp]
    congr 1
    exact LinearMap.ext hc
  have hsm : ∀ {S S' : LocLat G Qp LL O} (u : LatHom S.L S'.L) (c : LetA O f) (x : W.DD S),
      W.map u (c • x) = c • W.map u x := fun u c x => (W.map u).map_smul_of_tower c x
  have key : W.map g'' (b k : W.DD T) = ∑ q, (∑ m, a k m * a' m q) • (b'' q : W.DD T'') := by
    rw [hg, W.map_comp, h1 k, map_sum]
    simp_rw [hsm, h2, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
  have e : ∑ q, a'' k q • b'' q = ∑ q, (∑ m, a k m * a' m q) • b'' q := by
    apply (W.N T'').subtype_injective
    simpa [map_sum] using (h3 k).symm.trans key
  have := congrArg (fun x => b''.repr x p) e
  simpa [Finset.sum_apply, map_sum, Finsupp.smul_apply, b''.repr_self, Finsupp.single_apply] using this

end Gen

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem isMapMat_comp_mul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' T'' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' n'' : ℕ) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (b'' : Module.Basis (Fin n'') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T'')) (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L) (A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n) (A' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n') (A'' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n), IsMapMat (H.W K 1 LL hA.2.2) g b b' A → IsMapMat (H.W K 1 LL hA.2.2) g' b' b'' A' → IsMapMat (H.W K 1 LL hA.2.2) g'' b b'' A'' → (∀ x, g''.f x = g'.f (g.f x)) → ∀ i, A'' i = A' i * A i := by
  intro l _ P H K LL hA T T' T'' n n' n'' b b' b'' g g' g'' A A' A'' h1 h2 h3 hc i
  obtain ⟨hadd, hmul, hC, -, -, -, -, hinj⟩ := Formalism.CohomologicalDescent.FrobeniusPeriodChange.pi0Subst_laws_hold l ↥(OL LL)
  let incR : (↥(OL LL))⟦X⟧ →+* (↥(OL LL))⟦X⟧ :=
    { toFun := inc l ↥(OL LL)
      map_one' := by simpa using hC 1
      map_mul' := hmul
      map_zero' := by simpa using hC 0
      map_add' := hadd }
  refine Matrix.ext fun p k => hinj hA.2.1 ?_
  have e := congrFun (wachMap_comp_coeff (H.W K 1 LL hA.2.2) b b' b'' g g' g''
    (fun k m i => inc l ↥(OL LL) (A i m k)) (fun k m i => inc l ↥(OL LL) (A' i m k))
    (fun k m i => inc l ↥(OL LL) (A'' i m k)) h1 h2 h3 hc k p) i
  rw [Finset.sum_apply] at e
  rw [Matrix.mul_apply]
  refine e.trans (Eq.trans ?_ (map_sum incR _ _).symm)
  exact Finset.sum_congr rfl fun m _ => (mul_comm _ _).trans (hmul _ _).symm

end GlobalTheory.WachPlace
end
end

