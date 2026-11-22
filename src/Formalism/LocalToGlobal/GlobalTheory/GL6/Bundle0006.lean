import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0004

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionOfDecompGlob
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical

variable (D : D7) (u : D.what₂.Word)

theorem bwA_natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  first
    | exact lam.natW_anti
    | exact lam.anti
    | exact lam.antitone
    | (intro a b hab
       simp only [DomWeight.natW]
       first
         | (have := lam.anti hab; omega)
         | (have := lam.dom hab; omega)
         | (have := lam.antitone hab; omega)
         | (have := lam.mono hab; omega)
         | (have := lam.2 hab; omega)
         | (have := lam.dom a b hab; omega)
         | (have := lam.2 a b hab; omega)
         | (have := lam.w_anti hab; omega)
         | (have := lam.anti a b hab; omega))

theorem bwA_val_locInt (w : D.what₂.places.Pl) (σ : D.host.E →+* D.host.E) (y : D.host.E) (s : ℕ)
    (hs : ¬ D.what₂.places.resChar w ∣ s) (hy : (s : D.host.E) * y ∈ (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E).range) :
    (0 : WithTop ℤ) ≤ D.what₂.places.val w (D.embE (σ y)) := by
  obtain ⟨a, ha⟩ := hy
  have hint : IsIntegral ℤ (D.embE (σ (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E a))) :=
    (NumberField.RingOfIntegers.isIntegral_coe a).map ((D.embE.comp σ).toIntAlgHom)
  have h0 := bwA_val_integral_nonneg D.what₂.places w _ hint
  rw [ha, map_mul, map_mul, map_natCast, map_natCast, AddValuation.map_mul,
    bwA_val_nat_eq_zero D.what₂.places w s hs, zero_add] at h0
  exact h0

def BwBlock (Tt : FormsTied D u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v, (D.fm u).tauOf w v ∉ tops D →
    ∀ i (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B →
      IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B' →
      ∀ g ∈ delSq ℤ (D.R.N i) ((D.fm u).lam i ((D.fm u).tauOf w v)),
        (tpow D u (2 * Wt D u ((D.fm u).tauOf w v) + D.R.t) *
            (bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)).det ^
              shiftOf (lamT u i) ((D.fm u).tauOf w v)) •
          Formalism.GradedWeylDivisibility.rowAct ℂ (bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v))
            (MvPolynomial.map (Int.castRingHom ℂ) g) ∈
        bwA_span (bwA_Ow D w) le_rfl ((D.fm u).lam i ((D.fm u).tauOf w v)).natW

theorem bwA_subInt_of_block (Tt : FormsTied D u) (h : BwBlock D u Tt) : BwSubInt D u Tt := by
  unfold BwSubInt
  intro w hw hs v hv i hi c B B' hB hB' P hP
  have hN : ∀ τ, τ ≠ (D.fm u).tauOf w v → bwA_N D ((D.fm u).tauOf w v) B B' τ = 1 := by
    intro τ hτ
    simp [bwA_N, hτ]
  have hprod : (∏ τ, (bwA_N D ((D.fm u).tauOf w v) B B' τ).det ^ shiftOf (lamT u i) τ) =
      (bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)).det ^
        shiftOf (lamT u i) ((D.fm u).tauOf w v) := by
    rw [Finset.prod_eq_single ((D.fm u).tauOf w v)]
    · intro τ _ hτ
      rw [hN τ hτ, Matrix.det_one]
      first
        | exact one_pow _
        | exact one_zpow _
    · intro hm
      exact absurd (Finset.mem_univ _) hm
  rw [hprod, ← MvPolynomial.smul_eq_C_mul, smul_smul]
  exact bwA_intSpan_subP D w ((D.fm u).lam i) ((D.fm u).tauOf w v) _ hN _
    (h w hw hs v hv i hi c B B' hB hB') P hP

def bwA_EO (O : Subring ℂ) (N : ℕ) : Submonoid (Matrix (Fin N) (Fin N) ℂ) :=
  Submonoid.closure {g | ∃ (a b : Fin N) (c : ℂ), c ∈ O ∧ g = 1 + Matrix.single b a c}

def BwDecomp (Tt : FormsTied D u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v, (D.fm u).tauOf w v ∉ tops D →
    ∀ i (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B →
      IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B' →
      ∃ (K₁ K₂ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) (j : Fin (D.R.N i)) (p x : ℂ),
        K₁ ∈ bwA_EO (bwA_Ow D w) (D.R.N i) ∧ K₂ ∈ bwA_EO (bwA_Ow D w) (D.R.N i) ∧
        p ∈ bwA_Ow D w ∧ p ≠ 0 ∧ x ∈ bwA_Ow D w ∧
        bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v) = K₁ * Matrix.diagonal (Function.update 1 j p⁻¹) * K₂ ∧
        tpow D u (2 * Wt D u ((D.fm u).tauOf w v) + D.R.t) *
            (bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)).det ^
              shiftOf (lamT u i) ((D.fm u).tauOf w v) =
          x * p ^ ((D.fm u).lam i ((D.fm u).tauOf w v)).natW ⟨0, D.R.N_pos i⟩

theorem bwA_block_of_decomp (Tt : FormsTied D u) (h : BwDecomp D u Tt) : BwBlock D u Tt := by
  intro w hw hs v hv i hi c B B' hB hB' g hg
  obtain ⟨K₁, K₂, j, p, x, h₁, h₂, hpO, hp, hxO, hN, hc⟩ := h w hw hs v hv i hi c B B' hB hB'
  rw [hc, hN, mul_smul]
  have hg' : MvPolynomial.map (Int.castRingHom ℂ) g ∈
      bwA_span (bwA_Ow D w) le_rfl ((D.fm u).lam i ((D.fm u).tauOf w v)).natW :=
    Submodule.subset_span ⟨g, hg, rfl⟩
  have := bwA_span_sandwich (bwA_Ow D w) le_rfl _ (bwA_natW_anti _) (D.R.N_pos i) j p hpO hp K₁ K₂ h₁ h₂ _ hg'
  have e : x • (p ^ ((D.fm u).lam i ((D.fm u).tauOf w v)).natW ⟨0, D.R.N_pos i⟩ •
      Formalism.GradedWeylDivisibility.rowAct ℂ (K₁ * Matrix.diagonal (Function.update 1 j p⁻¹) * K₂) (MvPolynomial.map (Int.castRingHom ℂ) g)) =
      (⟨x, hxO⟩ : bwA_Ow D w) • (p ^ ((D.fm u).lam i ((D.fm u).tauOf w v)).natW ⟨0, D.R.N_pos i⟩ •
      Formalism.GradedWeylDivisibility.rowAct ℂ (K₁ * Matrix.diagonal (Function.update 1 j p⁻¹) * K₂) (MvPolynomial.map (Int.castRingHom ℂ) g)) := rfl
  rw [e]
  exact Submodule.smul_mem _ _ this

theorem lattice_inclusion_of_decomp_glob
    (h1 : ∀ (D : D7) (u : D.what₂.Word) (Tt : FormsTied D u), BwLocBases D u Tt)
    (h2 : ∀ (D : D7) (u : D.what₂.Word) (Tt : FormsTied D u), BwDecomp D u Tt)
    (h3 : ∀ (D : D7) (u : D.what₂.Word) (Tt : FormsTied D u), BwLocGlob D u Tt) : WeightLatticeInclusionFamily := lattice_inclusion_of_sub_integral h1 (fun D u Tt => bwA_subInt_of_block D u Tt (bwA_block_of_decomp D u Tt (h2 D u Tt))) h3

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.RndLinkAdmTOf
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem rnd_cls (S : StepLevel F E σ J T f bad) (γ0 : GL (Fin n) E) (hγ0 : γ0 ∈ UJ (σ : E →+* E) J)
    (y1 y2 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (k : S.U)
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ0 * y1.1 = y2.1 * k.1) :
    (Quotient.mk'' y1 : Cls S) = Quotient.mk'' y2 := by
  have hkU : k.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := ((S.U_eq k.1).1 k.2).1
  have e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ0 = y2.1 * k.1 * y1.1⁻¹ := by
    rw [← h]; group
  have hb : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ0 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
    rw [e]; exact Subgroup.mul_mem _ (Subgroup.mul_mem _ y2.2 hkU) (Subgroup.inv_mem _ y1.2)
  refine (DoubleCoset.eq _ _ y1 y2).2 ⟨⟨bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ0, hb⟩,
    ?_, ⟨k.1⁻¹, Subgroup.inv_mem _ hkU⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 ⟨γ0, hγ0, rfl⟩
  · exact Subgroup.mem_subgroupOf.2 (S.U.inv_mem k.2)
  · apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [h]; group

theorem rnd_chi (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hb : v ∉ bad)
    (η η' : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hη : ∀ v', v' ≠ v → bc (prV (E := E) v') η.1 = 1) (hη' : ∀ v', v' ≠ v → bc (prV (E := E) v') η'.1 = 1)
    (κ κ' k : S.U) (hk : k.1 = η.1 * κ.1 * η'.1 * κ'.1) : S.chi k = S.chi κ * S.chi κ' := by
  have key : S.chi ((κ * κ')⁻¹ * k) = 1 := by
    apply S.chi_triv
    intro v'' hv''
    have hne : v'' ≠ v := fun e => hb (e ▸ hv'')
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hk, map_mul, map_inv, hη v'' hne, hη' v'' hne, mul_one, one_mul]
    group
  rw [map_mul, map_inv, inv_mul_eq_one] at key
  rw [← key, map_mul]

end Gen

variable {D : D7} {u : D.what₂.Word}

def RndStab (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) c, RndStabTriv (Tf.cls i hi).lev ((Tf.cls i hi).y c)

set_option maxHeartbeats 2000000 in

def RUpLoc (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c ((Tf.lv i hi).pr v c z) = 1 →
    ∃ e : (D.fm u).lk i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lv i v c,
      e ((D.fm u).te i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))) = (Tf.lv i hi).pr v c z ∧
      ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
        (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
          ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c) →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c ⊔
            Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))))
          (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi c),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = (D.fm u).fv i v c ((Tf.lv i hi).pr v c ⟨_, hx⟩)) →
      ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
        (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
          ((Tf.cls i hi).y ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))
            (((D.fm u).fv i v c).comp e.toLinearMap))).1 =
          ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))).1 * η'.1 * κ'.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))
                  (((D.fm u).fv i v c).comp e.toLinearMap)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))
            (((D.fm u).fv i v c).comp e.toLinearMap))))
          (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) =
            (((D.fm u).fv i v c).comp e.toLinearMap)
              ((Tf.lv i hi).prk v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) ⟨_, hx⟩)) →
      η.1 * κ.1 * η'.1 * κ'.1 ∈ (Tf.cls i hi).lev.U

set_option maxHeartbeats 2000000 in

def RDnLoc (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ((D.fm u).te i v c) = 1 →
    ∃ e : (D.fm u).lv i v ((D.fm u).dn i v c g) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lk i v c,
      (D.fm u).fv i v ((D.fm u).dn i v c g) = g.comp e.toLinearMap ∧
      ∀ (z : ↥(Ld D u i hi ((D.fm u).dn i v c g))),
        (Tf.lv i hi).pr v ((D.fm u).dn i v c g) z = e.symm ((D.fm u).te i v c) →
      ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
        (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
          ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 = ((Tf.cls i hi).y c).1 * η'.1 * κ'.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
      ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
        (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
          ((Tf.cls i hi).y ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))).1 =
          ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 * η.1 * κ.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v)
                  (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi ((D.fm u).dn i v c g)) →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v)
                  (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi ((D.fm u).dn i v c g) ⊔
            Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))))
          (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi ((D.fm u).dn i v c g)),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) =
            (D.fm u).fv i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v ((D.fm u).dn i v c g) ⟨_, hx⟩)) →
      η'.1 * κ'.1 * η.1 * κ.1 ∈ (Tf.cls i hi).lev.U

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

