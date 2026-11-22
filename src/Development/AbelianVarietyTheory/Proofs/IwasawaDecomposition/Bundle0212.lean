import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0199
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0194

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalUnitaryPairToPairComponentMemLocalLevel
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LevelHecke.PairToLevel

theorem span_fun {A R M n : Type} [CommRing A] [CommRing R] [Algebra R A] [AddCommGroup M] [Module R M] [Fintype n]
    (Λ : Submodule R (n → A)) (f : Λ →ₗ[R] M) (B1 B2 : Matrix n n A) (S : Set (n → A))
    (h : ∀ w ∈ S, ∃ h1 h2, f ⟨B1 *ᵥ w, h1⟩ = f ⟨B2 *ᵥ w, h2⟩) :
    ∀ w ∈ Submodule.span R S, ∃ h1 h2, f ⟨B1 *ᵥ w, h1⟩ = f ⟨B2 *ᵥ w, h2⟩ := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero =>
    simp only [Matrix.mulVec_zero]
    exact ⟨zero_mem _, zero_mem _, trivial⟩
  | add a b _ _ ha hb =>
    obtain ⟨a1, a2, ha⟩ := ha
    obtain ⟨b1, b2, hb⟩ := hb
    simp only [Matrix.mulVec_add]
    refine ⟨add_mem a1 b1, add_mem a2 b2, ?_⟩
    have := congrArg₂ (· + ·) ha hb
    simp only [← map_add] at this
    exact this
  | smul a b _ hb =>
    obtain ⟨b1, b2, hb⟩ := hb
    simp only [Matrix.mulVec_smul]
    refine ⟨Λ.smul_mem a b1, Λ.smul_mem a b2, ?_⟩
    have := congrArg (a • ·) hb
    simp only [← map_smul] at this
    exact this

theorem unit_fun {A R M n : Type} [CommRing A] [CommRing R] [Algebra R A] [AddCommGroup M] [Module R M] [Fintype n]
    (Λ : Submodule R (n → A)) (f : Λ →ₗ[R] M) (B1 B2 : Matrix n n A) (w w' : n → A) (s : R) (e : w = s • w')
    (h : ∃ h1 h2, f ⟨B1 *ᵥ w', h1⟩ = f ⟨B2 *ᵥ w', h2⟩) :
    ∃ h1 h2, f ⟨B1 *ᵥ w, h1⟩ = f ⟨B2 *ᵥ w, h2⟩ :=
  span_fun Λ f B1 B2 {w'} (by rintro _ rfl; exact h) w (e ▸ Submodule.smul_mem _ s (Submodule.subset_span rfl))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem stabFun_gen {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {L1 L2 : Submodule (𝓞 E) (Fin n → E)}
    {M : Type} [AddCommGroup M] [Module (intV E v) M]
    (Λ : Submodule (intV E v) (Fin n → E ⊗[F] v.adicCompletion F)) (f : Λ →ₗ[intV E v] M)
    (y1 y2 : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy1 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L1 ↔ (y1⁻¹).1 *ᵥ x ∈ Λ)
    (hy2 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 ↔ (y2⁻¹).1 *ᵥ x ∈ Λ)
    (g : GL (Fin n) E)
    (hle : latS (F := F) (v.adicCompletion F) (intV E v) (mulLat g.1 L2) ≤
      latS (F := F) (v.adicCompletion F) (intV E v) L1)
    (hge : latS (F := F) (v.adicCompletion F) (intV E v) L1 ≤
      latS (F := F) (v.adicCompletion F) (intV E v) (mulLat g.1 L2))
    (hf : ∀ z ∈ L2, ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ ∃ h1 h2,
      f ⟨(y1⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((g.1 *ᵥ (algebraMap (𝓞 F) (𝓞 E) r • z)) a)), h1⟩ =
      f ⟨(y2⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) r • z) a)), h2⟩) :
    y1⁻¹ * bc (inclE (F := F) (v.adicCompletion F)) g * y2 ∈ stabFun Λ f := by
  have hG : ∀ x, (y1⁻¹ * bc (inclE (F := F) (v.adicCompletion F)) g * y2).1 *ᵥ x =
      (y1⁻¹).1 *ᵥ ((g.1.map (inclE (F := F) (v.adicCompletion F))) *ᵥ (y2.1 *ᵥ x)) := by
    intro x
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    rfl
  have hc : ∀ w, (y2⁻¹).1 *ᵥ (y2.1 *ᵥ w) = w := by
    intro w
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hY2 : ∀ w, w ∈ Λ ↔ y2.1 *ᵥ w ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 := by
    intro w
    rw [hy2, hc]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [hG]
    constructor
    · intro hx
      exact (hy1 _).1 (hle (rlv_latS_mulLat v _ L2 _ ((hY2 x).1 hx)))
    · intro hx
      have h1 := (hy1 _).2 hx
      have h2 := rlv_latS_mulLat v (g⁻¹).1 _ _ (hge h1)
      rw [rlv_mulLat_inv, rlv_map_inv_mul] at h2
      exact (hY2 x).2 h2
  · have hx2 : y2.1 *ᵥ x.1 ∈ Submodule.span (intV E v)
        ((fun x i => inclE (F := F) (v.adicCompletion F) (x i)) '' (L2 : Set (Fin n → E))) := by
      have := (hY2 x.1).1 x.2
      unfold latS at this
      exact this
    have key := span_fun Λ f ((y1⁻¹).1 * g.1.map (inclE (F := F) (v.adicCompletion F))) (y2⁻¹).1
      ((fun (x : Fin n → E) (i : Fin n) => inclE (F := F) (v.adicCompletion F) (x i)) '' (L2 : Set (Fin n → E))) ?_ (y2.1 *ᵥ x.1) hx2
    · obtain ⟨h1, h2, key⟩ := key
      convert key using 2
      · apply Subtype.ext
        show (y1⁻¹ * bc (inclE (F := F) (v.adicCompletion F)) g * y2).1 *ᵥ x.1 = _
        rw [hG, mulVec_mulVec]
      · exact Subtype.ext (hc _).symm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨r, hr, h1, h2, hf⟩ := hf z hz
      obtain ⟨s, hs, hsr⟩ := rlv_unit (E := E) v r hr
      refine unit_fun Λ f _ _ _
        (fun a => inclE (F := F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) r • z) a)) ⟨s, hs⟩ ?_ ?_
      · funext i
        show inclE (F := F) (v.adicCompletion F) (z i) = s * inclE (F := F) (v.adicCompletion F) (((algebraMap (𝓞 F) (𝓞 E) r) • z) i)
        rw [Pi.smul_apply, rlv_incl_smul]
        calc inclE (F := F) (v.adicCompletion F) (z i) = inclE (F := F) (v.adicCompletion F) (z i) * 1 := (mul_one _).symm
          _ = _ := by rw [← hsr]; ring
      · have e : ((y1⁻¹).1 * g.1.map (inclE (F := F) (v.adicCompletion F))) *ᵥ
            (fun a => inclE (F := F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) r • z) a)) =
            (y1⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((g.1 *ᵥ (algebraMap (𝓞 F) (𝓞 E) r • z)) a)) := by
          rw [← mulVec_mulVec]
          congr 1
          funext i
          exact (RingHom.map_mulVec _ _ _ _).symm
        refine ⟨e ▸ h1, h2, ?_⟩
        rw [← hf]
        congr 1
        exact Subtype.ext e

theorem loc_map {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k] (res : R →+* k)
    (g : V ≃ₗ[R] V) (M : Submodule R V) (x : V) :
    x ∈ loc res (M.map (g : V →ₗ[R] V)) ↔ g.symm x ∈ loc res M := by
  simp only [mem_loc, Submodule.mem_map_equiv, map_smul]

theorem mem_mulLat {E : Type} [Field E] {n : ℕ} (g : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (z : Fin n → E) (hz : z ∈ L) : g *ᵥ z ∈ mulLat g L := ⟨z, hz, rfl⟩

theorem exists_mul {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime]
    (hN : ∀ a : 𝓞 E, a ∉ P → a ∉ Q → ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ ∃ b : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) r = b * a)
    (g : Matrix (Fin n) (Fin n) E) (L M : Submodule (𝓞 E) (Fin n → E))
    (hP : Formalism.HermitianLatticesTheory.localization₂ P (mulLat g L) ≤ Formalism.HermitianLatticesTheory.localization₂ P M)
    (hQ : Formalism.HermitianLatticesTheory.localization₂ Q (mulLat g L) ≤ Formalism.HermitianLatticesTheory.localization₂ Q M) (z : Fin n → E) (hz : z ∈ L) :
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ g *ᵥ (algebraMap (𝓞 F) (𝓞 E) r • z) ∈ M := by
  obtain ⟨a, haP, haQ, hax⟩ := rlv_two P Q hP hQ (mem_mulLat g L z hz)
  obtain ⟨r, hr, b, hb⟩ := hN a haP haQ
  refine ⟨r, hr, ?_⟩
  rw [Matrix.mulVec_smul, hb, mul_smul]
  exact Submodule.smul_mem _ b hax

set_option synthInstance.maxHeartbeats 400000 in
theorem comp_eq {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (y y' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) :
    bc (prV (E := E) v) (y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y') =
      (bc (prV (E := E) v) y)⁻¹ * bc (inclE (F := F) (v.adicCompletion F)) γ * bc (prV (E := E) v) y' := by
  rw [map_mul, map_mul, map_inv]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem stabFun_loc {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {L1 L2 : Submodule (𝓞 E) (Fin n → E)}
    {M : Type} [AddCommGroup M] [Module (intV E v) M]
    (Λ : Submodule (intV E v) (Fin n → E ⊗[F] v.adicCompletion F)) (f : Λ →ₗ[intV E v] M)
    (y1 y2 : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy1 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L1 ↔ (y1⁻¹).1 *ᵥ x ∈ Λ)
    (hy2 : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L2 ↔ (y2⁻¹).1 *ᵥ x ∈ Λ)
    (g : GL (Fin n) E) (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime]
    (hN : ∀ a : 𝓞 E, a ∉ P → a ∉ Q → ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ ∃ b : 𝓞 E, algebraMap (𝓞 F) (𝓞 E) r = b * a)
    (hP : Formalism.HermitianLatticesTheory.localization₂ P (mulLat g.1 L2) = Formalism.HermitianLatticesTheory.localization₂ P L1)
    (hQ : Formalism.HermitianLatticesTheory.localization₂ Q (mulLat g.1 L2) = Formalism.HermitianLatticesTheory.localization₂ Q L1)
    (hf : ∀ w ∈ L2, g.1 *ᵥ w ∈ L1 → ∀ h1 h2,
      f ⟨(y1⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((g.1 *ᵥ w) a)), h1⟩ =
      f ⟨(y2⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (w a)), h2⟩) :
    y1⁻¹ * bc (inclE (F := F) (v.adicCompletion F)) g * y2 ∈ stabFun Λ f := by
  refine stabFun_gen v Λ f y1 y2 hy1 hy2 g (rlv_locV v P Q hN hP.le hQ.le) (rlv_locV v P Q hN hP.ge hQ.ge) ?_
  intro z hz
  obtain ⟨r, hr, m1⟩ := exists_mul v P Q hN g.1 L2 L1 hP.le hQ.le z hz
  have m2 : algebraMap (𝓞 F) (𝓞 E) r • z ∈ L2 := Submodule.smul_mem _ _ hz
  have n1 := (hy1 _).1 (Submodule.subset_span ⟨_, m1, rfl⟩)
  have n2 := (hy2 _).1 (Submodule.subset_span ⟨_, m2, rfl⟩)
  exact ⟨r, hr, n1, n2, hf _ m2 m1 n1 n2⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem main : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → (pc P v c').act (glE γ) = pc P v c → mov K (A.eV v).1 c γ c' ∈ K.lev.Uloc (A.eV v).1 := by
  intro D u A i hi P K fMe hT hJ v c c' γ hγ hpc
  have : (A.Pv v).IsPrime := RingHom.ker_isPrime _
  have hσσ : ∀ x, (sigD D : D.host.E →+* D.host.E) ((sigD D : D.host.E →+* D.host.E) x) = x := fun x => by
    show sigD D (sigD D x) = x
    rw [forms_involution_eq_host_conj, forms_involution_eq_host_conj, host_conj_involutive]
  have hL : ∀ x, (glE γ).symm x ∈ (pc P v c').L ↔ x ∈ (pc P v c).L := fun x => by
    rw [← hpc, Pr.mem_act]
  have hF : ∀ x, (pc P v c').f ((glE γ).symm x) = (pc P v c).f x := fun x => by
    rw [← hpc]; rfl
  have hfv : ∀ w (m2 : w ∈ Ld D u i hi c') (m1 : γ.1 *ᵥ w ∈ Ld D u i hi c),
      (D.fm u).fv i v c (P.pr v c ⟨_, m1⟩) = (D.fm u).fv i v c' (P.pr v c' ⟨_, m2⟩) := by
    intro w m2 m1
    rw [← locExt_coe (A.res v) _ (P.pr v c) (P.pr_smul v c), ← locExt_coe (A.res v) _ (P.pr v c') (P.pr_smul v c')]
    have h3 := hF (glE γ w)
    rw [LinearEquiv.symm_apply_apply] at h3
    exact h3.symm
  have hdP : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1 (Ld D u i hi c')) = Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Ld D u i hi c) := by
    ext x
    exact (loc_map (A.res v) (glE γ) (Ld D u i hi c') x).trans (hL x)
  have hP : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1 (clsCrd D u i hi c')) = Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (clsCrd D u i hi c) := by
    ext x
    refine (loc_map (A.res v) (glE γ) (clsCrd D u i hi c') x).trans ?_
    show _ ↔ x ∈ loc (A.res v) (clsCrd D u i hi c)
    rw [← GlobalTheory.LevelHecke.loc_lk_eq_loc_cls D u A i hi K v c, ← GlobalTheory.LevelHecke.loc_lk_eq_loc_cls D u A i hi K v c', pc_isKer P K v c, pc_isKer P K v c', hL, hF]
  have hPQ : ∀ a b : 𝓞 D.host.E, (b : D.host.E) = (sigD D : D.host.E →+* D.host.E) (a : D.host.E) →
      (a ∈ rlvQ A v ↔ b ∈ A.Pv v) := by
    intro a b hb
    have : b = RingOfIntegers.mapRingHom (sigD D : D.host.E →+* D.host.E) a := RingOfIntegers.ext hb
    rw [this]; rfl
  have hlat := bwB_clsCrd_lat D u i hi
  obtain ⟨hγL, hγd⟩ := (GlobalTheory.LevelHecke.DualConj.dual_conj_primes _ _ _ _ (A.Pv v) (rlvQ A v) hσσ (bwB_gramN_det D i hi) hJ hPQ _ _
    (hlat c') (hlat c)).2.2 γ hγ
  obtain ⟨k1, k2, -⟩ := GlobalTheory.LevelHecke.DualConj.dual_conj_primes _ _ _ _ (A.Pv v) (rlvQ A v) hσσ (bwB_gramN_det D i hi) hJ hPQ _ _ hγL (hlat c)
  have hdQ := k1 hP
  rw [hγd] at hdQ k2
  have hQ := k2 hdP
  have hN := rlv_norm A v
  have hU : (K.y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (K.y c').1 ∈
      UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    mul_mem (mul_mem (inv_mem (K.y c).2) (Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ, hγ, rfl⟩)) (K.y c').2
  have hLb : Submodule.IsLattice D.host.E K.lev.Lb :=
    ⟨(Submodule.fg_top _).1 K.lev.Lb_fin.fg_top, K.lev.Lb_span⟩
  have hy : ∀ c, ∀ x, x ∈ latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1) (Ld D u i hi c) ↔
      ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ x ∈ dualV K (A.eV v).1 := fun c =>
    GlobalTheory.DualCompletion.dual_move _ _ (sigD D) _ (gramN D i hi) (A.eV v).1 _ K.lev.Lb _ (bwB_gramN_det D i hi) (hlat c) hLb
      (Formalism.UG.P.afsplit_bc_mem _ _ _ _ (K.y c).2) (fun x => by
        rw [← map_inv]; exact rlv_yloc (A.eV v).1 (K.y c).1 (K.y_lat c) x)
  rw [K.lev.UlocAlt _ (A.eV v).2]
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Formalism.UG.P.afsplit_bc_mem _ _ _ _ hU, ?_⟩, ?_⟩
  · exact rlv_stab (A.eV v).1 (K.y c).1 (K.y c').1 (K.y_lat c) (K.y_lat c') γ
      (rlv_locV (A.eV v).1 (A.Pv v) (rlvQ A v) hN hP.le hQ.le)
      (rlv_locV (A.eV v).1 (A.Pv v) (rlvQ A v) hN hP.ge hQ.ge)
  · have e : mov K (A.eV v).1 c γ c' = (bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹ *
        bc (inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F)) γ * bc (prV (E := D.host.E) (A.eV v).1) (K.y c').1 :=
      comp_eq _ _ _ _
    rw [e]
    refine stabFun_loc (A.eV v).1 _ _ _ _ (hy c) (hy c') γ (A.Pv v) (rlvQ A v) hN hdP hdQ ?_
    intro w m2 m1 n1 n2
    exact (fMe v).injective ((hT v c ⟨_, m1⟩ n1).symm.trans ((hfv w m2 m1).trans (hT v c' ⟨_, m2⟩ n2)))

end GlobalTheory.LevelHecke.PairToLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductIntegralPureTensorEqProd
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdInt

theorem map_eq_smul_prod {ι Z Zi : Type} {Zv : ι → Type} [MeasurableSpace Z] [MeasurableSpace Zi]
    [∀ v, MeasurableSpace (Zv v)] (ρ : Measure Z) (mi : Measure Zi) (mv : ∀ v, Measure (Zv v))
    [SigmaFinite mi] [∀ v, SigmaFinite (mv v)] (pi : Z → Zi) (pv : ∀ v, Z → Zv v)
    (hpi : Measurable pi) (hpv : ∀ v, Measurable (pv v)) (S : Finset ι) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ (fi : Zi → ℝ≥0∞) (fv : ∀ v, Zv v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X, fi (pi X) * ∏ v ∈ S, fv v (pv v X) ∂ρ =
        (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * c) :
    ρ.map (fun X => (pi X, fun v : S => pv v X)) = c • mi.prod (Measure.pi fun v : S => mv v) := by
  classical
  have hT : Measurable (fun X => (pi X, fun v : S => pv v X)) :=
    hpi.prodMk (measurable_pi_lambda _ fun v => hpv v)
  by_cases hc0 : c = 0
  · have := h (fun _ => 1) (fun _ _ => 1) measurable_const (fun _ => measurable_const)
    simp only [hc0, mul_zero, Finset.prod_const_one, mul_one, lintegral_const, one_mul,
      Measure.measure_univ_eq_zero] at this
    simp [this, hc0]
  have key : mi.prod (Measure.pi fun v : S => mv v) =
      c⁻¹ • ρ.map (fun X => (pi X, fun v : S => pv v X)) := by
    refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
      (D := Set.pi Set.univ '' Set.pi Set.univ fun v : S => {s : Set (Zv v) | MeasurableSet s})
      MeasurableSpace.generateFrom_measurableSet generateFrom_pi
      MeasurableSpace.isPiSystem_measurableSet isPiSystem_pi mi.toFiniteSpanningSetsIn
      (Measure.FiniteSpanningSetsIn.pi fun v : S => (mv v).toFiniteSpanningSetsIn) ?_
    rintro s hs _ ⟨t, ht, rfl⟩
    have hs' : MeasurableSet s := hs
    have ht' : ∀ v : S, MeasurableSet (t v) := fun v => ht v (Set.mem_univ _)
    let fv : ∀ v, Zv v → ℝ≥0∞ := fun v => if hv : v ∈ S then (t ⟨v, hv⟩).indicator 1 else 0
    have hfv : ∀ v, Measurable (fv v) := by
      intro v
      by_cases hv : v ∈ S
      · simp only [fv, dif_pos hv]
        exact measurable_one.indicator (ht' _)
      · simp only [fv, dif_neg hv]
        exact measurable_zero
    have hfv' : ∀ v : S, fv v = (t v).indicator 1 := fun v => by simp only [fv, dif_pos v.2]
    have h1 := h (s.indicator 1) fv (measurable_one.indicator hs') hfv
    have hm : MeasurableSet (s ×ˢ Set.pi Set.univ t) :=
      hs'.prod (MeasurableSet.univ_pi ht')
    rw [Measure.smul_apply, Measure.map_apply hT hm, ← lintegral_indicator_one (hT hm), Measure.pi_pi]
    have h2 : ∀ X, ((fun X => (pi X, fun v : S => pv v X)) ⁻¹' (s ×ˢ Set.pi Set.univ t)).indicator
        (1 : Z → ℝ≥0∞) X = s.indicator 1 (pi X) * ∏ v ∈ S, fv v (pv v X) := by
      intro X
      rw [← Finset.prod_coe_sort S]
      simp only [hfv']
      by_cases hX : pi X ∈ s
      · by_cases hY : ∀ v : S, pv v X ∈ t v
        · rw [Set.indicator_of_mem (by simpa [hX] using hY)]
          simp [hX, hY]
        · rw [Set.indicator_of_notMem (by simpa [hX] using hY)]
          push_neg at hY
          obtain ⟨v, hv⟩ := hY
          rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])]
          simp
      · rw [Set.indicator_of_notMem (by simp [hX])]
        simp [hX]
    simp_rw [h2]
    rw [h1, ← Finset.prod_coe_sort S]
    simp only [hfv', lintegral_indicator_one hs', lintegral_indicator_one (ht' _), smul_eq_mul]
    rw [mul_comm c⁻¹, mul_assoc, ENNReal.mul_inv_cancel hc0 hc, mul_one]
  rw [key, smul_smul, ENNReal.mul_inv_cancel hc0 hc, one_smul]

theorem integral_tensor {ι Z Zi : Type} {Zv : ι → Type} [MeasurableSpace Z] [MeasurableSpace Zi]
    [∀ v, MeasurableSpace (Zv v)] (ρ : Measure Z) (mi : Measure Zi) (mv : ∀ v, Measure (Zv v))
    [SigmaFinite mi] [∀ v, SigmaFinite (mv v)] (pi : Z → Zi) (pv : ∀ v, Z → Zv v)
    (hpi : Measurable pi) (hpv : ∀ v, Measurable (pv v)) (S : Finset ι) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ (fi : Zi → ℝ≥0∞) (fv : ∀ v, Zv v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ X, fi (pi X) * ∏ v ∈ S, fv v (pv v X) ∂ρ =
        (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * c)
    (Φi : Zi → ℂ) (Φv : ∀ v, Zv v → ℂ) (hi : Integrable Φi mi) (hv : ∀ v, Integrable (Φv v) (mv v)) :
    Integrable (fun X => Φi (pi X) * ∏ v ∈ S, Φv v (pv v X)) ρ ∧
      ∫ X, Φi (pi X) * ∏ v ∈ S, Φv v (pv v X) ∂ρ =
        (∫ Y, Φi Y ∂mi) * ((∏ v ∈ S, ∫ Y, Φv v Y ∂(mv v)) * (c.toReal : ℂ)) := by
  have hT : Measurable (fun X => (pi X, fun v : S => pv v X)) :=
    hpi.prodMk (measurable_pi_lambda _ fun v => hpv v)
  have hmap := map_eq_smul_prod ρ mi mv pi pv hpi hpv S c hc h
  let G : Zi × (∀ v : S, Zv v) → ℂ := fun Y => Φi Y.1 * ∏ v : S, Φv v (Y.2 v)
  have hG : Integrable G (mi.prod (Measure.pi fun v : S => mv v)) :=
    hi.mul_prod (Integrable.fintype_prod_dep (f := fun v : S => Φv v) fun v => hv v)
  have hG' : Integrable G (ρ.map (fun X => (pi X, fun v : S => pv v X))) := by
    rw [hmap]; exact hG.smul_measure hc
  have he : (fun X => Φi (pi X) * ∏ v ∈ S, Φv v (pv v X)) =
      G ∘ (fun X => (pi X, fun v : S => pv v X)) := by
    funext X
    simp only [G, Function.comp]
    rw [← Finset.prod_coe_sort S]
  rw [he]
  refine ⟨(integrable_map_measure hG'.aestronglyMeasurable hT.aemeasurable).1 hG', ?_⟩
  have := integral_map hT.aemeasurable hG'.aestronglyMeasurable
  simp only [Function.comp_def]
  rw [← this, hmap, integral_smul_measure]
  simp only [G]
  rw [integral_prod_mul Φi (fun Y : ∀ v : S, Zv v => ∏ v : S, Φv v (Y v)),
    integral_fintype_prod_eq_prod (fun v : S => Φv v), ← Finset.prod_coe_sort S, Complex.real_smul]
  ring

theorem hasProd_of_tail {ι : Type} (f : ι → ℂ) (a : ι → ℝ) (ha : ∀ v, 0 ≤ a v)
    (hs : Summable fun v => |a v - 1|) (S : Finset ι) (hf : ∀ v ∉ S, f v = a v) :
    HasProd f ((∏ v ∈ S, f v) *
      (((ENNReal.ofReal (∏' v : {v // v ∉ S}, a v.1)).toReal : ℝ) : ℂ)) := by
  have hm : Multipliable fun v : {v // v ∉ S} => a v.1 := by
    have h1 : Summable fun v : {v // v ∉ S} => ‖a v.1 - 1‖ := hs.subtype _
    simpa using multipliable_one_add_of_summable h1
  have h0 : 0 ≤ ∏' v : {v // v ∉ S}, a v.1 :=
    ge_of_tendsto' hm.hasProd fun s => Finset.prod_nonneg fun v _ => ha _
  rw [ENNReal.toReal_ofReal h0]
  have h2 := hm.hasProd.map Complex.ofRealHom Complex.continuous_ofReal
  refine (S.hasProd f).mul_compl ?_
  have h3 : (f ∘ Subtype.val : {v // v ∉ S} → ℂ) = Complex.ofRealHom ∘ fun v : {v // v ∉ S} => a v.1 :=
    funext fun v => hf v.1 v.2
  have h4 : HasProd (f ∘ Subtype.val : {v // v ∉ S} → ℂ)
      ((∏' v : {v // v ∉ S}, a v.1 : ℝ) : ℂ) := by rw [h3]; exact h2
  exact h4

theorem integral_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Continuous Φinf → HasCompactSupport Φinf → IsPureFin b' Φf Φv → IsProdInfFin Φ Φinf Φf → Integrable Φ ν ∧ Multipliable (fun v => ∫ X, Φv v X ∂(mv v)) ∧ ∫ X, Φ X ∂ν = (∫ X, Φinf X ∂mi) * ∏' v, ∫ X, Φv v X ∂(mv v) := by
  intro F E _ _ _ _ _ d b n M ν mi mv hP d' b' Φ Φinf Φf Φv hc hcs hpure hΦ
  obtain ⟨⟨hmi, hmv, hsum⟩, hP⟩ := hP
  obtain ⟨hsb, hae, hfin⟩ := hpure
  obtain ⟨hco, -, hint, hbb⟩ := GlobalTheory.GaugeEx.IntBasis.main F E (AlgHom.id F E) d b
  obtain ⟨-, -, hci, hcv⟩ := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hae' : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1 := by
    filter_upwards [hae, hbb d' b'] with v h1 h2
    rw [h1]
    congr 1
    ext Y
    rw [mem_latV_iff, mem_latV_iff, h2]
  have hfinS := Filter.eventually_cofinite.1 hae'
  set S := hfinS.toFinset with hS
  have hout : ∀ v ∉ S, Φv v = (latV b v).indicator 1 := by
    intro v hv
    by_contra hne
    exact hv (by simpa [hS] using hne)
  have hlat : ∀ v : HeightOneSpectrum (𝓞 F),
      IsClosed (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
    intro v
    have : (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
        ⋂ a, ⋂ i, (fun Y => Y a i) ⁻¹' intV b v := by
      ext Y; simp [mem_latV_iff]
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun i =>
      (hco v).1.isClosed.preimage (by fun_prop)
  set B : Set (Fin n → Fin M → AF F ⊗[F] E) := {X | ∀ v ∉ S, projV v (projFin X) ∈ latV b v} with hB
  have hBm : MeasurableSet B := by
    have : B = ⋂ v, ⋂ (_ : v ∉ S), (fun X => projV v (projFin X)) ⁻¹' latV b v := by
      ext X; simp [hB]
    rw [this]
    exact (isClosed_iInter fun v => isClosed_iInter fun _ => (hlat v).preimage (hcv v)).measurableSet
  have hΦB : Φ = B.indicator fun X => Φinf (projInf X) * ∏ v ∈ S, Φv v (projV v (projFin X)) := by
    funext X
    rw [hΦ X, hfin]
    by_cases hX : X ∈ B
    · rw [Set.indicator_of_mem hX, finprod_eq_prod_of_mulSupport_subset (s := S)]
      intro v hv
      by_contra hvS
      have hvS' : v ∉ S := hvS
      apply hv
      simp only [hout v hvS']
      exact Set.indicator_of_mem (hX v hvS') _
    · rw [Set.indicator_of_notMem hX]
      simp only [hB, Set.mem_setOf_eq, not_forall] at hX
      obtain ⟨v, hvS, hv⟩ := hX
      have hev : ∀ᶠ v in Filter.cofinite, Φv v (projV v (projFin X)) = 1 := by
        have h1 : ∀ᶠ v in Filter.cofinite, ∀ a i, prV v (X a i) ∈ intV b v :=
          Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i => hint _
        filter_upwards [hae', h1] with w h2 h3
        rw [h2]
        exact Set.indicator_of_mem (show projV w (projFin X) ∈ latV b w from h3) _
      rw [finprod_eq_zero _ v (by rw [hout v hvS]; exact Set.indicator_of_notMem hv _)
        (Filter.eventually_cofinite.1 hev), mul_zero]
  haveI : SigmaFinite mi := inferInstance
  haveI : ∀ v, SigmaFinite (mv v) := fun v => inferInstance
  obtain ⟨h1, h2⟩ := integral_tensor (ν.restrict B) mi mv projInf (fun v X => projV v (projFin X))
    hci.measurable (fun v => (hcv v).measurable) S (tailProd b mv S) ENNReal.ofReal_ne_top (hP S)
    Φinf Φv (hc.integrable_of_hasCompactSupport hcs)
    (fun v => (hsb v).1.continuous.integrable_of_hasCompactSupport (hsb v).2)
  have h3 := hasProd_of_tail (fun v => ∫ X, Φv v X ∂(mv v)) (fun v => (mv v (latV b v)).toReal)
    (fun v => ENNReal.toReal_nonneg) hsum S (by
      intro v hv
      rw [hout v hv]
      have := integral_indicator_const (μ := mv v) (1 : ℂ) (hlat v).measurableSet
      simpa [Measure.real, Pi.one_def] using this)
  refine ⟨?_, h3.multipliable, ?_⟩
  · rw [hΦB]; exact (integrable_indicator_iff hBm).2 h1
  · rw [h3.tprod_eq, hΦB, integral_indicator hBm, h2]
    rfl

end GlobalTheory.GaugeEx.ProdInt
end

