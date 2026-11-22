import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064
import Formalism.LocalToGlobal.Columns.Bundle0005
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CauchyBinet.WwCauchyBinetMain
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
import Formalism.LocalToGlobal.HermitianForms.Bundle0003
import Formalism.LocalToGlobal.Columns.RecLevelLocT

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimePowSmulLeOfLocalizationsEqAway
section
noncomputable section

namespace GlobalTheory.InertExchange

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col

theorem exists_smul_mem_of_fg {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) (A B : Submodule R M) (hA : A.FG)
    (h : ∀ x ∈ A, ∃ s ∈ S, s • x ∈ B) : ∃ s ∈ S, ∀ x ∈ A, s • x ∈ B := by
  classical
  obtain ⟨G, rfl⟩ := hA
  have key : ∀ G' : Finset M, (G' : Set M) ⊆ G → ∃ s ∈ S, ∀ x ∈ Submodule.span R (G' : Set M), s • x ∈ B := by
    intro G'
    induction G' using Finset.induction_on with
    | empty => exact fun _ => ⟨1, S.one_mem, fun x hx => by
        simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hx
        simp [hx]⟩
    | insert a G' _ ih =>
      intro hsub
      simp only [Finset.coe_insert, Set.insert_subset_iff] at hsub
      obtain ⟨t, ht, hta⟩ := h a (Submodule.subset_span hsub.1)
      obtain ⟨s, hs, hsG⟩ := ih hsub.2
      refine ⟨t * s, S.mul_mem ht hs, fun x hx => ?_⟩
      rw [Finset.coe_insert, Submodule.mem_span_insert] at hx
      obtain ⟨r, y, hy, rfl⟩ := hx
      have e : (t * s) • (r • a + y) = (r * s) • (t • a) + t • (s • y) := by
        simp only [smul_add, smul_smul, mul_comm, mul_assoc, mul_left_comm]
      rw [e]
      exact B.add_mem (B.smul_mem _ hta) (B.smul_mem _ (hsG y hy))
  exact key G subset_rfl

theorem exists_smul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (B : Submodule (𝓞 E) (Sp E n)) (hB : Submodule.IsLattice E B) (x : Sp E n) :
    ∃ r ∈ nonZeroDivisors (𝓞 E), r • x ∈ B := by
  first
  | exact @_root_.GlobalTheory.SmulMemOfIsLattice.exists_smul_mem_of_isLattice
  | exact _root_.GlobalTheory.SmulMemOfIsLattice.exists_smul_mem_of_isLattice
  | (apply _root_.GlobalTheory.SmulMemOfIsLattice.exists_smul_mem_of_isLattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemOfIsLattice.exists_smul_mem_of_isLattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemOfIsLattice.exists_smul_mem_of_isLattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemOfIsLattice.exists_smul_mem_of_isLattice ..)

theorem exists_pow_smul_le_of_localization_eq {E : Type} [Field E] [NumberField E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)) (hA : A.FG)
    (hB : Submodule.IsLattice E B)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B) :
    ∃ k : ℕ, P.asIdeal ^ k • A ≤ B := by
  set I : Ideal (𝓞 E) := B.colon (A : Set (Sp E n)) with hIdef
  have hI0 : I ≠ ⊥ := by
    obtain ⟨s, hs, hsA⟩ := exists_smul_mem_of_fg (nonZeroDivisors (𝓞 E)) A B hA
      (fun x _ => exists_smul_mem_lattice B hB x)
    intro hI
    have hsI : s ∈ I := Submodule.mem_colon.2 hsA
    rw [hI, Ideal.mem_bot] at hsI
    exact nonZeroDivisors.ne_zero hs hsI
  have hIQ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → ¬ I ≤ Q.asIdeal := by
    intro Q hQ hle
    obtain ⟨s, hs, hsA⟩ := exists_smul_mem_of_fg Q.asIdeal.primeCompl A B hA (fun x hx => by
      have hxA : x ∈ localization₂ Q.asIdeal A := ⟨1, Q.asIdeal.primeCompl.one_mem, by simpa using hx⟩
      rw [h Q hQ] at hxA
      exact hxA)
    exact hs (hle (Submodule.mem_colon.2 hsA))
  have hrad : P.asIdeal ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro J ⟨hIJ, hJ⟩
    by_cases hJ0 : J = ⊥
    · exact absurd (le_bot_iff.1 (hJ0 ▸ hIJ)) hI0
    · let Q : HeightOneSpectrum (𝓞 E) := ⟨J, hJ, hJ0⟩
      by_cases hQ : Q = P
      · have : Q.asIdeal = P.asIdeal := by rw [hQ]
        exact le_of_eq this.symm
      · exact absurd hIJ (hIQ Q hQ)
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  exact ⟨k, Submodule.smul_le.2 fun r hr x hx => Submodule.mem_colon.1 (hk hr) x hx⟩

theorem exists_pow_smul_le_of_locP_eq :
    ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
      (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A → Submodule.IsLattice E B →
      (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B) →
      ∃ k : ℕ, P.asIdeal ^ k • A ≤ B ∧ P.asIdeal ^ k • B ≤ A := by
  intro E _ _ _ n P A B hA hB h
  obtain ⟨k₁, h₁⟩ := exists_pow_smul_le_of_localization_eq P A B hA.fg hB h
  obtain ⟨k₂, h₂⟩ := exists_pow_smul_le_of_localization_eq P B A hB.fg hA (fun Q hQ => (h Q hQ).symm)
  refine ⟨max k₁ k₂, ?_, ?_⟩
  · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_left k₁ k₂))).trans h₁
  · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right k₁ k₂))).trans h₂

end GlobalTheory.InertExchange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteOrbitsOfFiniteFibres
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2.StepOk

theorem finite_orbits_of_finite_fibres {G A B : Type} [Group G] [MulAction G A] [MulAction G B] (π : A → B)
    (hπ : ∀ (g : G) a, π (g • a) = g • π a) (hf : ∀ b, {a | π a = b}.Finite)
    [Finite (MulAction.orbitRel.Quotient G B)] : Finite (MulAction.orbitRel.Quotient G A) := by
  haveI : ∀ b, Finite {a | π a = b} := fun b => (hf b).to_subtype
  refine Finite.of_surjective (fun x : Σ q : MulAction.orbitRel.Quotient G B, {a | π a = q.out} =>
    (Quotient.mk _ x.2.1 : MulAction.orbitRel.Quotient G A)) ?_
  intro c
  induction c using Quotient.inductionOn' with
  | h a =>
    have h : (MulAction.orbitRel G B).r (Quotient.mk (MulAction.orbitRel G B) (π a)).out (π a) :=
      Quotient.exact (Quotient.out_eq _)
    obtain ⟨g, hg⟩ := h
    refine ⟨⟨Quotient.mk _ (π a), ⟨g • a, (hπ g a).trans hg⟩⟩, ?_⟩
    exact Quotient.sound ⟨g, rfl⟩

theorem ufGL_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) (x : Fin n → E) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x = γ.1 x :=
  LinearMap.toMatrix'_mulVec (γ.1 : Sp E n →ₗ[E] Sp E n) x

theorem ufGL_conjTranspose_mul {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)ᴴ *
      ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := by
  ext a b
  have h : ∑ i, star (γ.1 (Pi.single a 1) i) * γ.1 (Pi.single b 1) i =
      ∑ i, star ((Pi.single a 1 : Fin n → E) i) * (Pi.single b 1 : Fin n → E) i :=
    γ.2 (Pi.single a 1) (Pi.single b 1)
  have hv : ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
    LinearMap.toMatrix' (γ.1 : Sp E n →ₗ[E] Sp E n) := rfl
  rw [hv, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · rw [Finset.sum_eq_single a]
    · simp [Matrix.one_apply, Pi.single_apply]
    · intro c _ hc
      simp [Pi.single_apply, hc]
    · simp

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem levQ_root (Θ : LevQFam X.E X.K n Q) (h : ∀ P g, ∃ m : ℕ, 0 < m ∧ (Θ P).lam g ^ m = 1) (g : Θ.grp) :
    ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1 := by
  rw [← isOfFinOrder_iff_pow_eq_one]
  unfold LevQFam.chr piChar
  erw [MonoidHom.finsetProd_apply]
  refine Finset.prod_induction _ IsOfFinOrder (fun _ _ ha hb => ha.mul hb) IsOfFinOrder.one fun P _ => ?_
  rw [isOfFinOrder_iff_pow_eq_one]
  exact h P _

theorem eq_one_of_fst (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q) (g : FrmG Λ Θ)
    (hg : FrmG.incl Λ Θ g • p = p) (h1 : g.1 = 1) : g = 1 := by
  have hb : FrmG.incl Λ Θ 1 • p = p := by rw [map_one, one_smul]
  have h2 := DecoSet.stab_fst_injective p.deco (a := ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1))
    (b := ((FrmG.incl Λ Θ 1).1, (FrmG.incl Λ Θ 1).2.1)) (congrArg DecoF.deco hg) (congrArg DecoF.deco hb) h1
  exact FramedForms.incl_injective Λ Θ (FramedForms.stab_inj p hg hb h1 (Prod.mk.inj h2).2)

theorem stepY_ok : ∀ {X : Fields} {n : ℕ} {SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (y : Ys X n) (β : Type) [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q), X.Ok → ∀ (ST : Finset (HeightOneSpectrum (𝓞 X.E))) (pref : DecoF X.E n ST SG Q → Prop), (∀ b P, (Θ b P).H.FiniteIndex) → (∀ b P g, ∃ m : ℕ, 0 < m ∧ (Θ b P).lam g ^ m = 1) → (∀ N, Submodule.IsLattice X.E N → (y.ys N).Finite) → (stepY ST y β Λ Θ pref).Ok := by
  intro X n SG Q y β _ _ Λ Θ hX ST pref hfi hroot hfin
  have hG := fun b => FramedForms.main hX (ST := ST) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩) (Λ b) (Θ b) (hfi b)
    (levQ_root (Θ b) (hroot b))
  refine ⟨fun b => ?_, fun b p => ?_, fun b g => ?_, fun b g => ?_, fun b g p x => ?_, fun b p => ?_, fun b g p hg h1 => ?_⟩
  · letI := ptYAct (ST := ST) y (Λ b) (Θ b)
    haveI : Finite (MulAction.orbitRel.Quotient (FrmG (Λ b) (Θ b)) (DecoF X.E n ST SG Q)) := (hG b).fin_orb
    refine finite_orbits_of_finite_fibres (G := FrmG (Λ b) (Θ b)) (A := PtY ST SG Q y) (B := DecoF X.E n ST SG Q)
      (fun p => p.1.1) (fun _ _ => rfl) fun d => ?_
    refine Set.Finite.of_finite_image (f := fun p : PtY ST SG Q y => p.1.2) ?_ ?_
    · refine (hfin d.deco.1.N d.deco.2.1).subset ?_
      rintro _ ⟨p, hp, rfl⟩
      have hp' : p.1.1 = d := hp
      rw [← hp']
      exact p.2
    · intro p hp q hq h
      exact Subtype.ext (Prod.ext (hp.trans hq.symm) h)
  · letI := ptYAct (ST := ST) y (Λ b) (Θ b)
    haveI : Finite (MulAction.stabilizer (FrmG (Λ b) (Θ b)) p.1.1) := (hG b).fin_stab p.1.1
    refine Finite.of_injective (fun a : MulAction.stabilizer (FrmG (Λ b) (Θ b)) (show PtY ST SG Q y from p) =>
      (⟨a.1, congrArg (fun q : PtY ST SG Q y => q.1.1) a.2⟩ : MulAction.stabilizer (FrmG (Λ b) (Θ b)) p.1.1)) ?_
    intro a c h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  · exact ufGL_conjTranspose_mul g.1
  · obtain ⟨m, hm, hc⟩ := FramedForms.chr_root (Λ b) (Θ b) (levQ_root (Θ b) (hroot b)) g
    exact ⟨m, hm, Units.ext ((Units.val_pow_eq_pow_val _ _).trans hc)⟩
  · have h := p.1.1.deco.1.Lsh_act g.1.2 g.2.1.1
    show ((ufGL X.E n g.1 : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) *ᵥ x ∈ (p.1.1.deco.1.act g.1.1 g.2.1.1).Lsh ↔
      x ∈ p.1.1.deco.1.Lsh
    rw [h, ufGL_mulVec, mem_gmap, LinearEquiv.symm_apply_apply]
  · exact p.1.1.deco.2.Lsh_lattice
  · refine eq_one_of_fst (Λ b) (Θ b) p.1.1 g (congrArg (fun q : PtY ST SG Q y => q.1.1) hg) ?_
    have h2 : ufGL X.E n g.1 = 1 := h1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [← ufGL_mulVec, h2]
    simp

end GlobalTheory.Mem.Col2.StepOk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyFamOk
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix

section

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}

omit [NumberField K] [StarRing K] in

theorem GStep.lsh_eq_map (S : GStep E K n) (h : S.Ok) (b : S.β) (g : S.G b) (d : S.D b) :
    S.Lsh b (g • d) = (S.Lsh b d).map
      ((Matrix.mulVecLin (S.gam b g : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E)) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  have e : (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ (((S.gam b g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y = y := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  constructor
  · intro hy
    exact ⟨_, (h.lsh_smul b g d _).1 (by rw [e]; exact hy), e⟩
  · rintro ⟨x, hx, rfl⟩
    exact (h.lsh_smul b g d x).2 hx

omit [StarRing K] [Fintype ι] in

theorem GStep.tauLat_smul (S : GStep E K n) (h : S.Ok) (emb : ι → E →+* K) [Fintype ι] (b : S.β) (g : S.G b) (d : S.D b) (τ : ι) :
    tauLat emb τ (S.Lsh b (g • d)) = gLat (embGL emb (S.gam b g) τ) (tauLat emb τ (S.Lsh b d)) := by
  rw [S.lsh_eq_map h]
  exact tauLatG E K ι n emb τ _ (S.gam b g)

end

theorem fam_ok : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n),
    FOk emb σ → S.Ok → (S.fam emb lam).Ok := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF h b
  have hr : ∀ g : S.G b, ∃ m : ℕ, 0 < m ∧ ((S.chr b g : Kˣ) : K) ^ m = 1 := fun g => by
    obtain ⟨m, hm, hc⟩ := h.root b g
    exact ⟨m, hm, by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]⟩
  refine ⟨h.fin_orb b, h.fin_stab b, ?_, ?_, ?_⟩
  · intro g d
    obtain ⟨m, hm, hc⟩ := hr g
    refine Eq.trans ?_ (map_root_smul _ (rhoVr emb lam (S.gam b g)) hm hc).symm
    show nabAtr emb lam (S.Lsh b (g • d)) = (nabAtr emb lam (S.Lsh b d)).map _
    unfold nabAtr
    simp_rw [S.tauLat_smul h emb b g d, dualFr_gLat]
    exact nabK_gLat lam _ (invTrK (embGL emb (S.gam b g)))
  · intro g d
    obtain ⟨m, hm, hc⟩ := hr g
    refine Eq.trans ?_ (map_root_smul _ (rhoVr emb lam (S.gam b g)) hm hc).symm
    show delAtr emb lam (S.Lsh b (g • d)) = (delAtr emb lam (S.Lsh b d)).map _
    unfold delAtr
    simp_rw [S.tauLat_smul h emb b g d, dualFr_gLat]
    exact delK_gLat lam _ (invTrK (embGL emb (S.gam b g)))
  · intro g x y
    obtain ⟨m, hm, hc⟩ := hr g
    have hU : S.gam b g ∈ Formalism.UG.UJ (starRingEnd E) (1 : Matrix (Fin n) (Fin n) E) := by
      have := h.unit b g
      show _ * _ * _ = _
      rw [Matrix.mul_one]
      exact this
    have hi : pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) (rhoVr emb lam (S.gam b g) x) (rhoVr emb lam (S.gam b g) y) =
        pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) x y :=
      pairInv K ι n lam _ _ (fun τ => (uJUnitary E K ι n emb (starRingEnd E) τ
        (fun x => (hF.emb_star τ x).symm) 1 _ hU).2 (by simp)) x y
    show pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) (((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) x)
      (((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) y) = pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hi, smul_smul]
    show (star ((S.chr b g : Kˣ) : K) * _) • _ = _
    rw [star_mul_root ⟨σ, hF.sig_star⟩ hm hc, one_smul]

end GlobalTheory.Mem.Col2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyLawBasis
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms

section General

variable {K : Type} [Field K] (σ : K →+* ℂ) {V W C J : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]

theorem li_pi_of_basis [Finite C] [Fintype J] (e : Module.Basis J K V) (ev : V →ₛₗ[σ] W)
    (he : LinearIndependent ℂ fun j => ev (e j)) {κ : Type} (b : κ → C → V) (hb : LinearIndependent K b) :
    LinearIndependent ℂ fun i => fun c => ev (b i c) := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  let r : (C → V) →ₗ[K] (C × J → K) :=
    LinearMap.pi fun p => (e.coord p.2) ∘ₗ LinearMap.proj p.1
  have hr : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    funext c
    apply e.ext_elem
    intro j
    simpa [r] using congrFun hf (c, j)
  have h1 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 (hb.map' r hr)
  let T : (C × J → ℂ) →ₗ[ℂ] (C → W) :=
    LinearMap.pi fun c => ∑ j, (LinearMap.proj (c, j) : (C × J → ℂ) →ₗ[ℂ] ℂ).smulRight (ev (e j))
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    funext p
    have h2 : ∑ j, u (p.1, j) • ev (e j) = 0 := by
      simpa [T, LinearMap.sum_apply] using congrFun hu p.1
    exact Fintype.linearIndependent_iff.1 he (fun j => u (p.1, j)) h2 p.2
  have h3 := h1.map' T hT
  suffices hs : (fun i => fun c => ev (b i c)) = T ∘ fun i => algebraMap K ℂ ∘ (r ∘ b) i by
    rw [hs]
    exact h3
  funext i c
  have h4 : b i c = ∑ j, e.repr (b i c) j • e j := (e.sum_repr _).symm
  conv_lhs => rw [h4]
  simp only [map_sum, LinearMap.map_smulₛₗ]
  simp [T, r, LinearMap.sum_apply, RingHom.algebraMap_toAlgebra]

theorem mem_span_basis_image [Fintype J] (e : Module.Basis J K V) (ev : V →ₛₗ[σ] W) (x : V) :
    ev x ∈ Submodule.span ℂ (Set.range fun j => ev (e j)) := by
  rw [← e.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem rho_sum_translates {G : Type} [Group G] [Fintype G] (ρ : G →* Module.End K V) (g : G) (x : V) :
    ρ g (∑ t, ρ t x) = ∑ t, ρ t x := by
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun t => ?_
  simp [map_mul]

end General

namespace GStep

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

omit [StarRing E] [StarRing K] in

theorem evV_rho_eq_tr (b : S.β) (g : S.G b) (F : VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g F) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ F) := by
  funext y
  have h1 : S.rho emb lam b g F = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) F := rfl
  rw [h1, LinearMap.map_smulₛₗ, tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb _ lam σ _ F y _ ?_
  have h2 : y = frMul emb σ (S.gam b g) (frMul emb σ (S.gam b g)⁻¹ y) := by
    rw [← frMul_mul, mul_inv_cancel, frMul_one]
  intro τ
  exact congrFun (congrArg Subtype.val h2) τ

theorem lawBasis_of_ok (h : (S.fam emb lam).Ok) : S.LawBasis emb σ lam h := by
  classical
  haveI : Fintype S.Cl := h.fintypeCl
  constructor
  · have h1 : LinearIndependent K fun a => ((S.csd emb lam h).basis a).1 :=
      (S.csd emb lam h).basis.linearIndependent.map' (S.csd emb lam h).Forms.subtype (Submodule.ker_subtype _)
    exact li_pi_of_basis σ (C := S.Cl) (S.csd emb lam h).bV (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ)
      (evV_linearIndependent emb _ lam σ (fr0 emb σ n) _ (S.csd emb lam h).bV.linearIndependent) _ h1
  · refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩ c
      refine ⟨evV_mem_ValC emb _ lam σ _, fun g => ?_⟩
      have h1 := ((S.csd emb lam h).basis a).2 c g
      have h2 := S.evV_rho_eq_tr emb σ lam c.1 g.1 (((S.csd emb lam h).basis a).1 c)
      exact h2.symm.trans (congrArg (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ) h1)
    · intro φ hφ
      rw [← Finset.univ_sum_single φ]
      refine Submodule.sum_mem _ fun c _ => ?_
      letI : Fintype (S.Stab c) := (S.csd emb lam h).finGam c
      let A : (Fr emb σ n → ℂ) →ₗ[ℂ] (S.Cl → Fr emb σ n → ℂ) :=
        LinearMap.single ℂ (fun _ : S.Cl => Fr emb σ n → ℂ) c ∘ₗ ∑ g : S.Stab c, (S.tr emb σ c.1 g.1).toLinearMap
      have hA : ∀ w, A w = Pi.single c (∑ g : S.Stab c, S.tr emb σ c.1 g.1 w) := fun w => by
        simp [A, LinearMap.sum_apply]
      have hle : ValC (Gr emb σ n) lam ≤ (Submodule.span ℂ
          (Set.range fun a => S.embF emb σ lam h ((S.hlat emb lam h).b a))).comap A := by
        rw [← span_evV, Submodule.span_le]
        rintro _ ⟨F, rfl⟩
        let ρc : S.Stab c →* Module.End K (VV K lam) :=
          (S.rho emb lam c.1).comp (MulAction.stabilizer (S.G c.1) (S.rep c)).subtype
        let x : S.FormsK emb lam h := ⟨(Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam), by
          intro c' γ
          by_cases hc : c' = c
          · subst hc
            show ρc γ ((Pi.single c' (∑ t, ρc t F) : S.Cl → VV K lam) c') =
              (Pi.single c' (∑ t, ρc t F) : S.Cl → VV K lam) c'
            rw [Pi.single_eq_same]
            exact rho_sum_translates ρc γ F
          · show S.rho emb lam c'.1 γ.1 ((Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c') =
              (Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c'
            rw [Pi.single_eq_of_ne hc, map_zero]⟩
        have hx : A (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ F) = S.embF emb σ lam h x := by
          rw [hA]
          funext c'
          show _ = evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ ((Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c')
          by_cases hc : c' = c
          · subst hc
            rw [Pi.single_eq_same, Pi.single_eq_same, map_sum]
            exact Finset.sum_congr rfl fun g _ => (S.evV_rho_eq_tr emb σ lam c'.1 g.1 F).symm
          · rw [Pi.single_eq_of_ne hc, Pi.single_eq_of_ne hc, map_zero]
        rw [SetLike.mem_coe, Submodule.mem_comap, hx]
        exact mem_span_basis_image σ (S.hlat emb lam h).b (S.embF emb σ lam h) x
      have h1 := Submodule.mem_comap.1 (hle (hφ c).1)
      have h2 : A (φ c) = (Fintype.card (S.Stab c) : ℂ) • (Pi.single c (φ c) : S.Cl → Fr emb σ n → ℂ) := by
        rw [hA, Finset.sum_congr rfl fun g _ => (hφ c).2 g, Finset.sum_const, Finset.card_univ, ← Pi.single_smul',
          Nat.cast_smul_eq_nsmul]
      rw [h2] at h1
      exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)).1 h1

end GStep

theorem lawBasis_all : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n),
    FOk emb σ → S.Ok → ∀ h, S.LawBasis emb σ lam h :=
  fun S emb σ lam _ _ h => S.lawBasis_of_ok emb σ lam h

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncreasingRowChoicePerColumn
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

abbrev IncreasingRowChoicePerColumn (N : ℕ) (Y : YoungDiagram) : Type := ∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N

def sig {Lt : Type} (N : ℕ) (s : Lt) : Fin N × Fin N → Lt × ℕ × Fin N := fun v => (s, (v.2 : ℕ), v.1)

theorem map_nablaX {Lt : Type} [Fintype Lt] (K : Type) [CommRing K] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (J : WeylLatticeDuality.ColChoice N nu) :
    map (Int.castRingHom K) (WeylLatticeDuality.nablaX N nu J) =
      ∏ s, rename (sig N s) (GlobalTheory.WeylMinorDual.colProd K N (nu s) (hY s) (J s)) := by
  unfold WeylLatticeDuality.nablaX GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext1 p q
  simp [sig]

theorem colLen_le_of_rowLen {N : ℕ} {Y : YoungDiagram} (h : Y.rowLen N = 0) : Y.colLen 0 ≤ N := by
  by_contra hc'
  have hc := not_le.mp hc'
  have h1 : (N, 0) ∈ Y := YoungDiagram.mem_iff_lt_colLen.mpr hc
  have h2 := YoungDiagram.mem_iff_lt_rowLen.mp h1
  omega

end GlobalTheory.WeylLatDualProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelActsTriviallyOnDiscriminantGroupStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_acts_trivially_on_discriminant_group : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (_ : ∀ x, σ (σ x) = x) {n : ℕ} [NeZero n] {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ (1 : Matrix (Fin n) (Fin n) E) T f bad) (p q : 𝓞 E) (_ : (q : E) = σ (p : E)) (_ : (p : E) * (q : E) = (T : E)) (_ : T ≠ 0)
    (_ : S.Lb = rll_dLat n ((p : E)⁻¹))
    (_ : Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb) = rll_dLat n (q : E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (_ : ∀ m : S.fM v hv, m ≠ 0 → ∀ d c : intV E v, (d - 1) • m = 0 →
      sigR σ (v.adicCompletion F) (d : E ⊗[F] v.adicCompletion F) * (d : E ⊗[F] v.adicCompletion F) =
        1 + (T : E ⊗[F] v.adicCompletion F) * (c : E ⊗[F] v.adicCompletion F) →
      ∃ e : intV E v, (d : E ⊗[F] v.adicCompletion F) = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F))
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (_ : x ∈ S.Uloc v),
    ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  first | exact @GlobalTheory.uloc_acts_trivially_on_dual_quotient | exact GlobalTheory.uloc_acts_trivially_on_dual_quotient | (intros; apply GlobalTheory.uloc_acts_trivially_on_dual_quotient <;> assumption)
end

