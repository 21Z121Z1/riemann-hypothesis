import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyClassDiesOnLocalizationAway
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonPicEtaleLocalizationUnitsModuloStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_pic_etale_localization_unitsModulo : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], Subsingleton (CommRing.Pic (Localization (Algebra.algebraMapSubmonoid A' ((IsUnit.submonoid (B ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f)))) := by
  first | (exact @GlobalTheory.PicLoc.subsingleton_pic_localization) | (exact GlobalTheory.PicLoc.subsingleton_pic_localization) | (intros; apply GlobalTheory.PicLoc.subsingleton_pic_localization <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyClassDiesOnLocalizationAwayStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_class_dies_on_localizationAway : B1 → ∀ (q : ℕ) (A : Type) [CommRing A] (M : Submonoid A) (n i : ℤ), IsUnit (q : A) → ∀ m ∈ M, ∀ y : Ht q (sp (Localization.Away m)) n i, ∀ φ : Localization.Away m →+* Localization M, φ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap φ) _ _ y = 0 → ∃ m' ∈ M, ∀ ψ : Localization.Away m →+* Localization.Away (m * m'), ψ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ψ) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.AwayCont.kill_of_loc) | (exact GlobalTheory.EtC.AwayCont.kill_of_loc) | (intros; apply GlobalTheory.EtC.AwayCont.kill_of_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionSurjectiveEigen
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem projEigenspaceEquiv (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (Λ : Type)
    [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (σ : Λ →+* O) (f : RL p O Λ →+* O)
    (ρ : Λ → Matrix (Fin h) (Fin h) (Ainf p O))
    (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O))
    (π : (Fin h → C) →ₗ[C] (Fin N → C)) :
    Function.Injective (algebraMap O C) → Function.Surjective (WittVector.fontaineTheta O p) →
    Function.Surjective f → IsTheta σ f → IsFrame ρ e → IsProj C e f π →
    (⨆ s : Λ →+* O, eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s) = ⊤ →
    Module.finrank C (eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ) = N →
    ∃ q : eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ ≃ₗ[C] (Fin N → C),
      (∀ x, q x = π x) ∧ ∀ x, x ∈ quotLattice C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ ↔
        ∀ i, q x i ∈ (algebraMap O C).range := by
  intro hinj hθ hf hth hfr hpr hsup hrank
  have hkill : ∀ z ∈ ⨆ s : {s : Λ →+* O // s ≠ σ},
      eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s.1, π z = 0 :=
    GlobalTheory.T.theta_projection_eigen_image p O C Λ N h σ f ρ e π hinj hth hfr hpr
  have hdec : ∀ z : Fin h → C, ∃ x ∈ eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ,
      ∃ z' ∈ ⨆ s : {s : Λ →+* O // s ≠ σ},
        eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s.1, x + z' = z := by
    intro z
    have hsplit : (⨆ s : Λ →+* O, eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s) =
        eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ ⊔
          ⨆ s : {s : Λ →+* O // s ≠ σ},
            eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s.1 := by
      rw [iSup_split_single _ σ, iSup_subtype']
    have hz : z ∈ eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ ⊔
          ⨆ s : {s : Λ →+* O // s ≠ σ},
            eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) s.1 := by
      rw [← hsplit, hsup]; trivial
    exact Submodule.mem_sup.mp hz
  have hπsurj : Function.Surjective π := by
    obtain ⟨r, hr⟩ := hf 1
    have hs : ∀ i : Fin N, Pi.single i (1 : C) ∈ LinearMap.range π := by
      intro i
      refine ⟨fun j => algebraMap O C (WittVector.fontaineTheta O p (e (Pi.single i r) j)), ?_⟩
      rw [hpr]
      ext k
      by_cases hk : k = i
      · subst hk; simp [hr]
      · simp [Pi.single_apply, hk]
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun C (Fin N)).span_eq,
      Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simpa using hs i
  let π₀ : eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ →ₗ[C] (Fin N → C) :=
    π ∘ₗ (eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ).subtype
  have hsurj : Function.Surjective π₀ := by
    intro v
    obtain ⟨z, rfl⟩ := hπsurj v
    obtain ⟨x, hx, z', hz', rfl⟩ := hdec z
    exact ⟨⟨x, hx⟩, by simp [π₀, map_add, hkill z' hz']⟩
  have hinj0 : Function.Injective π₀ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hrank, Module.finrank_fin_fun])).mpr hsurj
  let q := LinearEquiv.ofBijective π₀ ⟨hinj0, hsurj⟩
  have hq : ∀ x, q x = π x := fun x => rfl
  refine ⟨q, hq, fun x => ?_⟩
  simp only [quotLattice, Set.mem_setOf_eq, RingHom.mem_range, hq]
  constructor
  · rintro ⟨t, ht⟩
    have hlift : ∀ j, ∃ a : Ainf p O, WittVector.fontaineTheta O p a = t j := fun j => hθ (t j)
    choose a ha using hlift
    have h1 : π (fun j => algebraMap O C (t j)) = fun i => algebraMap O C (f (e.symm a i)) := by
      have := hpr (e.symm a)
      simpa [ha] using this
    have h2 := hkill _ ht
    rw [map_sub, sub_eq_zero, h1] at h2
    intro i
    exact ⟨f (e.symm a i), by rw [← h2]⟩
  · intro hx
    choose c hc using hx
    have hlift : ∀ i, ∃ r, f r = c i := fun i => hf (c i)
    choose w hw using hlift
    refine ⟨fun j => WittVector.fontaineTheta O p (e w j), ?_⟩
    obtain ⟨x', hx', z', hz', hsum⟩ :=
      hdec (fun j => algebraMap O C (WittVector.fontaineTheta O p (e w j)))
    have h1 := hpr w
    have hqq : q ⟨x', hx'⟩ = q x := by
      rw [hq, hq]
      have : π (x' + z') = π x' := by rw [map_add, hkill z' hz', add_zero]
      rw [← this, hsum, h1]
      funext i
      simp [hw, ← hc i]
    have hxx : (⟨x', hx'⟩ : eig C (fun l => (ρ l).map (WittVector.fontaineTheta O p)) σ) = x :=
      q.injective hqq
    have hz : (fun j => algebraMap O C (WittVector.fontaineTheta O p (e w j))) -
        (x : Fin h → C) = z' := by
      rw [← hsum, ← hxx]; simp
    rw [hz]; exact hz'

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDifferentialEval
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.total_differential_eval : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1), (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫ (tot Y).d (k + 1) k = ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫ (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  first | (exact @GlobalTheory.EZ.ιTotal_tot_d) | (exact GlobalTheory.EZ.ιTotal_tot_d) | (intros; apply GlobalTheory.EZ.ιTotal_tot_d <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceWedgePairingPerfectRationalForms
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

theorem wedge_pairing_sep {K V : Type} [Field K] [AddCommGroup V] [Module K V] {p q : ℕ}
    (b : Module.Basis (Fin (p + q)) K V) (τ : ExteriorAlgebra K V →ₗ[K] K)
    (hτ : τ (ExteriorAlgebra.ιMulti K (p + q) b) ≠ 0) (y : ExteriorAlgebra K V) (hy : y ∈ ⋀[K]^q V)
    (h : ∀ a ∈ ⋀[K]^p V, τ (a * y) = 0) : y = 0 := by
  classical
  have hdet : ∀ v : Fin (p + q) → V,
      τ (ExteriorAlgebra.ιMulti K (p + q) v) = τ (ExteriorAlgebra.ιMulti K (p + q) b) * b.det v := by
    intro v
    have e := congrArg (fun f => f v)
      (AlternatingMap.eq_smul_basis_det b (τ.compAlternatingMap (ExteriorAlgebra.ιMulti K (p + q))))
    simpa [mul_comm] using e
  have htop : ∀ U : Set.powersetCard (Fin (p + q)) (p + q),
      τ (ExteriorAlgebra.ιMulti_family K (p + q) b U) ≠ 0 := by
    intro U
    set e := Set.powersetCard.ofFinEmbEquiv.symm U
    have hinj : Function.Injective e := e.injective
    have hbij : Function.Bijective e := ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
    let σ := Equiv.ofBijective e hbij
    have hb : (b ∘ e) = ⇑(b.reindex σ.symm) := by
      funext i; simp [σ]
    rw [ExteriorAlgebra.ιMulti_family, hdet, hb]
    exact mul_ne_zero hτ (b.isUnit_det _).ne_zero
  have hcoe : ∀ {n : ℕ} (I : Set.powersetCard (Fin (p + q)) n),
      ((Module.Basis.exteriorPower n b I : ⋀[K]^n V) : ExteriorAlgebra K V) =
        ExteriorAlgebra.ιMulti_family K n b I := by
    intro n I
    simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family, ExteriorAlgebra.ιMulti_family]
  set B := Module.Basis.exteriorPower q b
  set Y : ⋀[K]^q V := ⟨y, hy⟩
  suffices hY : B.repr Y = 0 by
    have : Y = 0 := B.repr.injective (by rw [hY, map_zero])
    exact congrArg Subtype.val this
  ext J
  have hJc : (J.valᶜ : Finset (Fin (p + q))).card = p := by
    rw [Finset.card_compl, Fintype.card_fin, show (J.val).card = q from J.prop]; omega
  let Jc : Set.powersetCard (Fin (p + q)) p := ⟨J.valᶜ, by simpa using hJc⟩
  have hdisj : Disjoint Jc.val J.val := disjoint_compl_left
  set a : ExteriorAlgebra K V := ExteriorAlgebra.ιMulti_family K p b Jc
  have ha : a ∈ ⋀[K]^p V := by
    rw [show a = _ from (hcoe Jc).symm]; exact (Module.Basis.exteriorPower p b Jc).2
  have hy' : y = ∑ I, B.repr Y I • (ExteriorAlgebra.ιMulti_family K q b I) := by
    have := congrArg Subtype.val (B.sum_repr Y)
    change (Y : ExteriorAlgebra K V) = _
    rw [← this, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Submodule.coe_smul, hcoe]
  have key := h a ha
  rw [hy', Finset.mul_sum, map_sum, Finset.sum_eq_single J] at key
  · rw [mul_smul_comm, map_smul, ExteriorAlgebra.ιMulti_family_mul_of_disjoint _ _ _ _ hdisj,
      Units.smul_def, map_zsmul, smul_eq_mul] at key
    rcases mul_eq_zero.1 key with h0 | h0
    · simpa using h0
    · exfalso
      rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint hdisj).sign with hs | hs <;>
        rw [hs] at h0 <;> simp at h0 <;> exact htop _ h0
  · intro I _ hI
    rw [mul_smul_comm, ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint, smul_zero, map_zero]
    intro hd
    apply hI
    have hsub : I.val ⊆ J.val := by
      intro i hi
      by_contra hj
      exact Finset.disjoint_left.1 hd (show i ∈ J.valᶜ from Finset.mem_compl.2 hj) hi
    have hle : J.val.card ≤ I.val.card := by
      rw [show (I.val).card = q from I.prop, show (J.val).card = q from J.prop]
    exact Subtype.ext (Finset.eq_of_subset_of_card_le hsub hle)
  · intro hJ; exact absurd (Finset.mem_univ J) hJ

end GlobalTheory.PD

namespace GlobalTheory.PD

theorem IsFinCover.trace_wedge_perfect : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ p q : ℕ, p + q = d → (∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ ⋀[K]^p Ω[K⁄k], Algebra.trace F K (τ (a * y)) = 0) → y = 0) ∧ Module.finrank K (⋀[K]^p Ω[K⁄k]) = Module.finrank K (⋀[K]^q Ω[K⁄k]) ∧ FiniteDimensional K (⋀[K]^p Ω[K⁄k]) := by
  intro k _ _ F K _ _ _ _ _ _ d x h τ hτ p q hpq
  haveI := h.fin
  haveI := h.sep
  obtain ⟨b, hb⟩ := h.exists_basis
  haveI : Module.Finite K Ω[K⁄k] := Module.Finite.of_basis b
  haveI : Module.Free K Ω[K⁄k] := Module.Free.of_basis b
  have hfr : Module.finrank K Ω[K⁄k] = d := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  refine ⟨fun y hy hy0 => ?_, ?_, inferInstance⟩
  · have hτb : τ (ExteriorAlgebra.ιMulti K d b) ≠ 0 := by
      intro h0
      have hv : vol0 k K x =
          (∏ j : Fin d, (algebraMap F K (x j.succ / x 0))⁻¹) • ExteriorAlgebra.ιMulti K d b := by
        rw [← AlternatingMap.map_smul_univ]
        simp only [vol0, hb]
      have h1 := hτ.1
      rw [hv, map_smul, h0, smul_zero] at h1
      exact zero_ne_one h1
    have h2 : ∀ a ∈ ⋀[K]^p Ω[K⁄k], τ (a * y) = 0 := by
      intro a ha
      refine (traceForm_nondegenerate F K).1 _ fun c => ?_
      rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← map_smul, ← smul_mul_assoc]
      exact hy0 _ (Submodule.smul_mem _ c ha)
    subst hpq
    exact wedge_pairing_sep b τ hτb y hy h2
  · rw [exteriorPower.finrank_eq, exteriorPower.finrank_eq, hfr]
    exact Nat.choose_symm_of_eq_add hpq.symm

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def trivV (N : ℕ) (E : Spc) : E ⟶ ofCat (glCat N) where
  app n :=
    { app := fun U => TypeCat.ofHom fun _ =>
        (show Fin (n.unop.len + 1) ⥤ (glCat N).obj (Scheme.Γ.obj U) from
          (CategoryTheory.Functor.const _).obj (SingleObj.star (GL (Fin N) (Scheme.Γ.obj U))))
      naturality := fun U U' f => by
        ext x
        exact CategoryTheory.Functor.hext (fun _ => rfl)
          (fun _ _ _ => heq_of_eq (map_one (Matrix.GeneralLinearGroup.map _)).symm) }
  naturality n m f := by
    ext U x
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq rfl)

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationDescendAwayStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_away_unit_map_eq : ∀ (A : Type) [CommRing A] (M : Submonoid A) (u : (Localization M)ˣ), ∃ m ∈ M, ∃ v : (Localization.Away m)ˣ, ∀ φ : Localization.Away m →+* Localization M, φ.comp (algebraMap A _) = algebraMap A _ → Units.map φ.toMonoidHom v = u := by
  first | (exact @GlobalTheory.units_localization_descend_away) | (exact GlobalTheory.units_localization_descend_away) | (intros; apply GlobalTheory.units_localization_descend_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeChartChange
section
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR

namespace GlobalTheory.PD

section Alt

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem altMap_add_smul_self {n : ℕ} (f : M [⋀^Fin n]→ₗ[R] N) (v : Fin n → M) (k : Fin n) (c : Fin n → R)
    (hc : c k = 0) : f (fun j => v j + c j • v k) = f v := by
  classical
  have key : ∀ s : Finset (Fin n), f (fun j => v j + if j ∈ s then c j • v k else 0) = f v := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      by_cases hak : a = k
      · subst hak
        have e : (fun j => v j + if j ∈ insert a s then c j • v a else 0) =
            (fun j => v j + if j ∈ s then c j • v a else 0) := by
          funext j
          by_cases hj : j = a
          · subst hj; simp [hc]
          · simp [Finset.mem_insert, hj]
        rw [e, ih]
      · set g : Fin n → M := fun j => v j + if j ∈ s then c j • v k else 0 with hg
        have e1 : (fun j => v j + if j ∈ insert a s then c j • v k else 0) = Function.update g a (v a + c a • v k) := by
          funext j
          by_cases hj : j = a
          · subst hj; simp
          · simp [hg, Function.update_of_ne hj, Finset.mem_insert, hj]
        have e2 : Function.update g a (v a) = g := by
          funext j
          by_cases hj : j = a
          · subst hj; simp [hg, ha]
          · simp [Function.update_of_ne hj]
        have e3 : f (Function.update g a (v k)) = 0 := by
          refine f.map_eq_zero_of_eq _ (i := a) (j := k) ?_ hak
          simp [Function.update_of_ne (Ne.symm hak), hg, hc]
        rw [e1, f.map_update_add, f.map_update_smul, e2, ih, e3, smul_zero, add_zero]
  simpa using key Finset.univ

theorem exists_perm_succ {d : ℕ} (τ : Fin d → Fin (d + 1)) (hinj : Function.Injective τ) (hne : ∀ j, τ j ≠ 0) :
    ∃ π : Equiv.Perm (Fin d), τ = Fin.succ ∘ π := by
  let p : Fin d → Fin d := fun j => (τ j).pred (hne j)
  have hp : Function.Injective p := by
    intro a b hab
    apply hinj
    simpa [p] using congrArg Fin.succ hab
  refine ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.1 hp), ?_⟩
  funext j
  simp [p]

theorem altMap_sub_succAbove {d : ℕ} (f : M [⋀^Fin d]→ₗ[R] N) (θ : Fin (d + 1) → M) (h0 : θ 0 = 0)
    (i : Fin (d + 1)) : ∃ ε : ℤˣ, f (fun j => θ (i.succAbove j) - θ i) = ε • f (fun j => θ j.succ) := by
  classical
  cases i using Fin.cases with
  | zero => exact ⟨1, by simp [h0]⟩
  | succ i' =>
    have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) i'.isLt
    set i : Fin (d + 1) := i'.succ with hi
    set j0 : Fin d := ⟨0, hd⟩ with hj0
    have hσ0 : i.succAbove j0 = 0 := by
      rw [Fin.succAbove_of_castSucc_lt]
      · rfl
      · rw [Fin.lt_def]; simp [hi, hj0]
    set w : Fin d → M := fun j => θ (i.succAbove j) - θ i with hw
    set c : Fin d → R := fun j => if j = j0 then 0 else -1 with hc
    have k1 := altMap_add_smul_self f w j0 c (by simp [hc])
    have e1 : (fun j => w j + c j • w j0) = Function.update (θ ∘ i.succAbove) j0 ((-1 : R) • θ i) := by
      funext j
      by_cases hj : j = j0
      · subst hj; simp [hw, hc, hσ0, h0]
      · simp [hw, hc, hj, hσ0, h0, Function.update_of_ne hj]
    set τ : Fin d → Fin (d + 1) := Function.update i.succAbove j0 i with hτ
    have e2 : Function.update (θ ∘ i.succAbove) j0 (θ i) = θ ∘ τ := by
      funext j
      by_cases hj : j = j0
      · subst hj; simp [hτ]
      · simp [hτ, Function.update_of_ne hj]
    have hτinj : Function.Injective τ := by
      intro a b hab
      by_cases ha : a = j0 <;> by_cases hb : b = j0
      · rw [ha, hb]
      · simp [hτ, ha, Function.update_of_ne hb] at hab
      · simp [hτ, hb, Function.update_of_ne ha] at hab
      · simp only [hτ, Function.update_of_ne ha, Function.update_of_ne hb] at hab
        exact Fin.succAbove_right_injective hab
    have hτne : ∀ j, τ j ≠ 0 := by
      intro j
      by_cases hj : j = j0
      · subst hj; simp [hτ, hi]
      · rw [hτ, Function.update_of_ne hj, ← hσ0]
        exact fun h => hj (Fin.succAbove_right_injective h)
    obtain ⟨π, hπ⟩ := exists_perm_succ τ hτinj hτne
    refine ⟨-Equiv.Perm.sign π, ?_⟩
    rw [← k1, e1, f.map_update_smul, e2, hπ]
    have e3 : θ ∘ (Fin.succ ∘ ⇑π) = (fun j => θ j.succ) ∘ ⇑π := rfl
    rw [e3, f.map_perm, Units.neg_smul, neg_one_smul]

end Alt

theorem volume_chart_change (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) (h : IsFinCover k K x)
    (i : Fin (d + 1)) : ∃ ε : ℤˣ, (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (x (i.succAbove j) / x i))) =
      ε • algebraMap F K (∏ j, x j / x i) • vol0 k K x := by
  have hx := h.pd.ne
  set y : Fin (d + 1) → K := fun a => algebraMap F K (x a / x 0) with hy
  have hy0 : ∀ a, y a ≠ 0 := fun a => (map_ne_zero _).2 (div_ne_zero (hx a) (hx 0))
  set θ : Fin (d + 1) → Ω[K⁄k] := fun a => (y a)⁻¹ • D k K (y a) with hθ
  have hθ0 : θ 0 = 0 := by
    show (algebraMap F K (x 0 / x 0))⁻¹ • D k K (algebraMap F K (x 0 / x 0)) = 0
    rw [div_self (hx 0), map_one, Derivation.map_one_eq_zero, smul_zero]
  have hD : ∀ a, D k K (algebraMap F K (x a / x i)) = algebraMap F K (x a / x i) • (θ a - θ i) := by
    intro a
    have e : algebraMap F K (x a / x i) = y a / y i := by
      simp only [hy, ← map_div₀]
      congr 1
      field_simp [hx 0, hx i]
    have ha := hy0 a
    have hi := hy0 i
    rw [e, Derivation.leibniz_div, hθ]
    simp only [smul_sub, smul_smul]
    congr 2 <;> field_simp
  obtain ⟨ε, hε⟩ := altMap_sub_succAbove (ExteriorAlgebra.ιMulti K d) θ hθ0 i
  refine ⟨ε, ?_⟩
  have hprod : algebraMap F K (∏ j, x j / x i) = ∏ j, algebraMap F K (x (i.succAbove j) / x i) := by
    rw [Fin.prod_univ_succAbove _ i, div_self (hx i), one_mul, map_prod]
  simp only [hD]
  rw [AlternatingMap.map_smul_univ, hε, hprod]
  rw [smul_comm]
  rfl

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassDivisionValueQExpansion
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ExpansionB

theorem val_div_ne_int (N : ℕ) [NeZero N] (j : ZMod N) (hj : j ≠ 0) (n : ℤ) :
    ((j.val : ℂ)) / N ≠ n := by
  intro h
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [div_eq_iff hN] at h
  have h' : (j.val : ℤ) = n * (N : ℤ) := by exact_mod_cast h
  apply hj
  have h2 := congrArg (Int.cast : ℤ → ZMod N) h'
  simpa using h2

theorem main : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), x ≠ 0 → HasQ N (wB N x) (cB N x) := by
  classical
  intro N _ x hx
  rw [hasQ_iff]
  intro τ
  obtain ⟨T, hT, hS⟩ := GlobalTheory.T.torsionPoint_rows_sum_eq_divisor_series N 1 τ x _ le_rfl (GlobalTheory.T.G2_add_weierstrassP_row_sum τ (tors N τ x))
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hT' : HasSum (fun k : ℕ => cSum N 1 1 x k *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ k) T := by
    simpa using hT
  set c : ℂ := (if x 0 = 0 then ch N (x 1) / (1 - ch N (x 1)) ^ 2 else 0) with hcdef
  have hval : wB N x τ = T + c := by
    rw [wB_eq, hS, div_eq_iff (pow_ne_zero 2 hc), hcdef]
    by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := by
        intro h1
        apply hx
        funext i
        fin_cases i
        · exact h0
        · exact h1
      have him : (((x 1).val : ℂ) / N).im = 0 := by
        have : (((x 1).val : ℂ) / N) = ((((x 1).val : ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.ofReal_im]
      have hr := (GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger _ him (val_div_ne_int N (x 1) h1)).1
      have hch : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((x 1).val : ℂ) / N)) = ch N (x 1) := by
        rw [ch, mul_div_assoc]
      rw [hch] at hr
      rw [if_pos h0, if_pos h0]
      have e2 : (1 + 1 : ℕ) = 2 := rfl
      rw [e2, hr]
      simp only [Nat.factorial_one, Nat.cast_one]
      ring
    · rw [if_neg h0, if_neg h0]
      simp only [Nat.factorial_one, Nat.cast_one]
      ring
  rw [hval]
  have hs : HasSum (fun k : ℕ => if k = 0 then c else 0) c := hasSum_ite_eq 0 c
  convert hT'.add hs using 2 with k
  by_cases hk : k = 0
  · subst hk
    simp [cB, cSum, hcdef]
  · simp [cB, hk]

end GlobalTheory.WpFam.ExpansionB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLeastSquaresBoundStatement
section
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_weighted_least_squares_le : ∀ (M g : ℕ) (L : Matrix (Fin M) (Fin g) ℝ), L.rank = g → ∃ K : ℝ, ∀ (D : Fin M → ℝ) (b : Fin M → ℝ), (∀ k, 0 < D k) → ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖ ≤ K * ‖b‖ := by
  first | exact @GlobalTheory.WeightedLS.weighted_least_squares_bound | exact GlobalTheory.WeightedLS.weighted_least_squares_bound | (intros; apply GlobalTheory.WeightedLS.weighted_least_squares_bound <;> assumption)
end

