import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquarefreePrimeSumExceptional
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalLevelVectorLaws
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.TDat

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) {T : ℕ}

theorem exists_fv (h : A.Ok T) (P : ST) (c : S.Cl) :
    ∃ φ : Module.Dual (Res P.1) (A.lv P c), ∀ x : A.N c.1 (S.rep c),
      φ (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  let g : A.N c.1 (S.rep c) →ₗ[𝓞 E] Res P.1 :=
    { toFun := fun x => A.f c.1 (S.rep c) P x
      map_add' := fun x y => h.f_add _ _ _ _ x.2 _ y.2
      map_smul' := fun a x => by
        have := h.f_smul _ _ P a _ x.2
        simp only [RingHom.id_apply]
        rw [Submodule.coe_smul, this]
        rfl }
  have hk : P.1.asIdeal • (⊤ : Submodule (𝓞 E) (A.N c.1 (S.rep c))) ≤ LinearMap.ker g := by
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    show Ideal.Quotient.mk P.1.asIdeal a * g x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  let g' : A.lv P c →ₗ[𝓞 E] Res P.1 := Submodule.liftQ _ g hk
  refine ⟨{ toFun := g', map_add' := g'.map_add, map_smul' := ?_ }, fun x => rfl⟩
  intro r x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact g'.map_smul a x

theorem fv_mk (h : A.Ok T) (P : ST) (c : S.Cl) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  have hx := A.exists_fv h P c
  unfold fv
  rw [dif_pos hx]
  exact hx.choose_spec x

theorem fv_ne_zero (h : A.Ok T) (P : ST) (c : S.Cl) : A.fv P c ≠ 0 := by
  obtain ⟨x, hx, hne⟩ := h.f_ne c.1 (S.rep c) P
  intro h0
  have := A.fv_mk h P c ⟨x, hx⟩
  rw [h0] at this
  exact hne this.symm

theorem exists_f_eq_one (h : A.Ok T) (b : S.β) (d : S.D b) (P : ST) : ∃ e ∈ A.N b d, A.f b d P e = 1 := by
  obtain ⟨x, hx, hne⟩ := h.f_ne b d P
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (A.f b d P x)⁻¹
  refine ⟨a • x, (A.N b d).smul_mem a hx, ?_⟩
  rw [h.f_smul b d P a x hx, ha]
  exact inv_mul_cancel₀ hne

theorem te_ne_zero (h : A.Ok T) (P : ST) (c : S.Cl) : A.te T P c ≠ 0 := by
  have hx : ∃ t : A.dnN c.1 (S.rep c) P, ∃ e ∈ A.N c.1 (S.rep c), A.f c.1 (S.rep c) P e = 1 ∧
      (t : Fin n → E) = (T : 𝓞 E) • e := by
    obtain ⟨e, he, h1⟩ := A.exists_f_eq_one h c.1 (S.rep c) P
    exact ⟨⟨_, (h.te_mem _ _ P e he h1).1⟩, e, he, h1, rfl⟩
  unfold te
  rw [dif_pos hx]
  obtain ⟨e, he, h1, ht⟩ := hx.choose_spec
  intro h0
  rw [Submodule.Quotient.mk_eq_zero] at h0
  apply (h.te_mem _ _ P e he h1).2
  rw [← ht]
  have := Submodule.mem_map_of_mem (f := (A.dnN c.1 (S.rep c) P).subtype) h0
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at this
  exact this

end GlobalTheory.Mem.Col2.TDat

namespace GlobalTheory.Mem.Col2

theorem fv_te_laws : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T →
    (∀ P c (x : A.N c.1 (S.rep c)), A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x) ∧
    (∀ P c, A.fv P c ≠ 0) ∧ ∀ P c, A.te T P c ≠ 0 :=
  fun A _ _ h => ⟨A.fv_mk h, A.fv_ne_zero h, A.te_ne_zero h⟩

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexForms
section
noncomputable section

namespace GlobalTheory.Mem.Col2.DiaStab

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix

section General

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem tr_one (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  funext y
  simp [GStep.tr, trFr_apply, frMul_one]

theorem evV_rho (b : S.β) (g : S.G b) (v : VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g v) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) := by
  funext y
  have h : S.rho emb lam b g v = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) v := rfl
  rw [h, LinearMap.map_smulₛₗ, GStep.tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb 1 lam σ _ v y _ ?_
  have := congrArg Subtype.val ((frEquiv emb σ (S.gam b g)).apply_symm_apply y)
  intro τ
  exact (congrFun this τ).symm

theorem tr_mem (b : S.β) (g : S.G b)
    {F : Fr emb σ n → ℂ} (hF : F ∈ ValC (Gr emb σ n) lam) : S.tr emb σ b g F ∈ ValC (Gr emb σ n) lam := by
  rw [← span_evV emb 1 lam σ] at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [← evV_rho]
    exact evV_mem_ValC emb 1 lam σ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem mem_Fi (hf : S.Free)
    (φ : S.Cl → Fr emb σ n → ℂ) (h : ∀ c, φ c ∈ ValC (Gr emb σ n) lam) : φ ∈ S.Fi emb σ lam := fun c =>
  ⟨h c, fun g => by rw [hf c.1 g.1 _ g.2, tr_one]⟩

end General

theorem lawDiaStable : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R),
    FOk emb σ → ∀ (_hI : I.Ok), J.Ok → J.LawDiaStable emb σ hc := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc _ _ h
  rintro P a _ ⟨φ, hφ, rfl⟩
  exact mem_Fi _ emb σ _ h.free0 _ fun c => tr_mem _ emb σ _ _ _ (hφ _).1

end GlobalTheory.Mem.Col2.DiaStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesIntegralForms
section
namespace GlobalTheory.Mem.Col2.DiaLat

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

section General

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem evV_rho_tr (b : S.β) (g : S.G b) (v : VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g v) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) := by
  funext y
  have h : S.rho emb lam b g v = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) v := rfl
  rw [h, LinearMap.map_smulₛₗ, GStep.tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb 1 lam σ _ v y _ ?_
  have := congrArg Subtype.val ((frEquiv emb σ (S.gam b g)).apply_symm_apply y)
  intro τ
  exact (congrFun this τ).symm

theorem exists_pull (hf : S.Free) (h : (S.fam emb lam).Ok) (p : ∀ c : S.Cl, S.D c.1)
    (hp : ∀ c, S.Lsh c.1 (p c) = S.Lsh c.1 (S.rep c)) (x : S.FormsK emb lam h) (hx : x ∈ (S.hlat emb lam h).L) :
    ∃ y ∈ (S.hlat emb lam h).L, ∀ c, S.embF emb σ lam h y c =
      S.trTo emb σ c.1 (p c) (S.embF emb σ lam h x (S.cl c.1 (p c))) := by
  refine ⟨⟨fun c => S.rho emb lam c.1 (S.mv c.1 (p c)) (x.1 (S.cl c.1 (p c))), fun c g => ?_⟩, fun c => ?_, fun c => ?_⟩
  · have hg : (g.1 : S.G c.1) = 1 := hf c.1 g.1 (S.rep c) g.2
    show S.rho emb lam c.1 g.1 _ = _
    rw [hg, map_one]
    rfl
  · have h1 : delAtr emb lam (S.Lsh c.1 (S.mv c.1 (p c) • S.rep (S.cl c.1 (p c)))) =
        (delAtr emb lam (S.Lsh c.1 (S.rep (S.cl c.1 (p c))))).map
          ((S.rho emb lam c.1 (S.mv c.1 (p c))).restrictScalars (𝓞 K)) :=
      (h c.1).del_smul (S.mv c.1 (p c)) (S.rep (S.cl c.1 (p c)))
    rw [S.mv_smul, hp] at h1
    show S.rho emb lam c.1 (S.mv c.1 (p c)) (x.1 (S.cl c.1 (p c))) ∈ delAtr emb lam (S.Lsh c.1 (S.rep c))
    rw [h1]
    exact Submodule.mem_map_of_mem (hx (S.cl c.1 (p c)))
  · exact evV_rho_tr S emb σ lam c.1 _ _

end General

theorem dia_lat : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (hF : ((I.S 0).fam emb (lamT hc 0)).Ok) P a x, x ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L → ∃ y ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L, (I.S 0).embF emb σ (lamT hc 0) hF y = J.diaLin emb σ P a ((I.S 0).embF emb σ (lamT hc 0) hF x) := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc _ _ hJ hF P a x hx
  obtain ⟨y, hy, e⟩ := exists_pull (I.S 0) emb σ (lamT hc 0) hJ.free0 hF (fun c => (J.A 0).diaPt P a c)
    (fun c => (hJ.lev 0).dia_Lsh c.1 P a _) x hx
  exact ⟨y, hy, funext e⟩

end GlobalTheory.Mem.Col2.DiaLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondRepresentation
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.DiaRep

set_option linter.unusedSectionVars false

section Step

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ)

theorem trFr_mul_apply (γ δ : GL (Fin n) E) (c d : Kˣ) (F : Fr emb σ n → ℂ) :
    trFr emb σ (γ * δ) (c * d) F = trFr emb σ γ c (trFr emb σ δ d F) := by
  funext y
  simp only [trFr_apply, mul_inv_rev, frMul_mul, Units.val_mul, map_mul, mul_assoc]

theorem trFr_one_apply (F : Fr emb σ n → ℂ) : trFr emb σ (1 : GL (Fin n) E) (1 : Kˣ) F = F := by
  funext y
  simp only [trFr_apply, inv_one, frMul_one, Units.val_one, map_one, one_mul]

theorem tr_mul_apply (b : S.β) (g h : S.G b) (F : Fr emb σ n → ℂ) :
    S.tr emb σ b (g * h) F = S.tr emb σ b g (S.tr emb σ b h F) := by
  unfold GStep.tr
  rw [map_mul, map_mul, trFr_mul_apply]

theorem tr_one_apply (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  unfold GStep.tr
  rw [map_one, map_one, trFr_one_apply]

theorem mk_smul (b : S.β) (g : S.G b) (d : S.D b) :
    Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) (g • d) = Quotient.mk _ d :=
  Quotient.sound ⟨g, rfl⟩

theorem mv_smul' (b : S.β) (d : S.D b) : S.mv b d • S.rp b (Quotient.mk _ d) = d := S.mv_smul b d

theorem eq_of_free (hf : S.Free) (b : S.β) (g h : S.G b) (d : S.D b) (e : g • d = h • d) : g = h := by
  have h1 : (h⁻¹ * g) • d = d := by rw [mul_smul, e, inv_smul_smul]
  have h2 := hf b _ d h1
  exact (inv_mul_eq_one.1 h2).symm

theorem mv_smul_eq (hf : S.Free) (b : S.β) (g : S.G b) (d : S.D b) : S.mv b (g • d) = g * S.mv b d := by
  apply eq_of_free S hf b _ _ (S.rp b (Quotient.mk _ d))
  have h1 := mv_smul' S b (g • d)
  rw [mk_smul] at h1
  rw [h1, mul_smul, mv_smul']

theorem mv_rp (hf : S.Free) (b : S.β) (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) : S.mv b (S.rp b q) = 1 := by
  apply hf b _ (S.rp b q)
  have h1 := mv_smul' S b (S.rp b q)
  rwa [S.rp_spec] at h1

def evPt (φ : S.Cl → Fr emb σ n → ℂ) (b : S.β) (d : S.D b) : Fr emb σ n → ℂ :=
  S.tr emb σ b (S.mv b d) (φ ⟨b, Quotient.mk _ d⟩)

theorem evPt_smul (hf : S.Free) (φ : S.Cl → Fr emb σ n → ℂ) (b : S.β) (g : S.G b) (d : S.D b) :
    evPt S emb σ φ b (g • d) = S.tr emb σ b g (evPt S emb σ φ b d) := by
  unfold evPt
  rw [mv_smul_eq S hf, tr_mul_apply, mk_smul]

theorem evPt_rep (hf : S.Free) (φ : S.Cl → Fr emb σ n → ℂ) (c : S.Cl) :
    evPt S emb σ φ c.1 (S.rep c) = φ c := by
  obtain ⟨b, q⟩ := c
  show S.tr emb σ b (S.mv b (S.rp b q)) (φ ⟨b, Quotient.mk _ (S.rp b q)⟩) = φ ⟨b, q⟩
  rw [mv_rp S hf, tr_one_apply, S.rp_spec]

end Step

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ)

theorem diaLin_apply (P : J.ST) (a : (Res P.1)ˣ) (φ : (I.S 0).Cl → Fr emb σ (R.N 0) → ℂ) (c : (I.S 0).Cl) :
    J.diaLin emb σ P a φ c = evPt (I.S 0) emb σ φ c.1 ((J.A 0).dia c.1 P a ((I.S 0).rep c)) := rfl

theorem evPt_diaLin (h : J.Ok) (P : J.ST) (a : (Res P.1)ˣ) (φ : (I.S 0).Cl → Fr emb σ (R.N 0) → ℂ)
    (b : (I.S 0).β) (d : (I.S 0).D b) :
    evPt (I.S 0) emb σ (J.diaLin emb σ P a φ) b d = evPt (I.S 0) emb σ φ b ((J.A 0).dia b P a d) := by
  have h1 : evPt (I.S 0) emb σ (J.diaLin emb σ P a φ) b d = (I.S 0).tr emb σ b ((I.S 0).mv b d)
      (evPt (I.S 0) emb σ φ b ((J.A 0).dia b P a ((I.S 0).rp b (Quotient.mk _ d)))) := rfl
  rw [h1, ← evPt_smul _ _ _ h.free0, ← (h.lev 0).dia_act, mv_smul']

theorem lawDiaOne (h : J.Ok) : J.LawDiaOne emb σ := by
  intro P
  refine LinearMap.ext fun φ => funext fun c => ?_
  rw [diaLin_apply, (h.lev 0).dia_one, evPt_rep _ _ _ h.free0]
  rfl

theorem lawDiaMul (h : J.Ok) : J.LawDiaMul emb σ := by
  intro P a b
  refine LinearMap.ext fun φ => funext fun c => ?_
  rw [Module.End.mul_apply, diaLin_apply, diaLin_apply, evPt_diaLin J emb σ h, ← (h.lev 0).dia_mul, mul_comm b a]

theorem diamond_rep : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R),
    FOk emb σ → ∀ (hI : I.Ok), J.Ok → J.LawDiaOne emb σ ∧ J.LawDiaMul emb σ :=
  fun _ J emb σ _ _ _ h => ⟨lawDiaOne J emb σ h, lawDiaMul J emb σ h⟩

end GlobalTheory.Mem.Col2.DiaRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationHermitianDualEq
section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

namespace GlobalTheory.DualLoc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem hStd_osmul_right (y : Sp E n) (c : 𝓞 E) (z : Sp E n) :
    hStd E n y (c • z) = c • hStd E n y z := by
  rw [← algebraMap_smul E c z, map_smul, algebraMap_smul]

theorem mem_localization_dual_iff (Q : HeightOneSpectrum (𝓞 E)) (L : Submodule (𝓞 E) (Sp E n)) (hL : L.FG) (x : Sp E n) :
    x ∈ localization₂ Q.asIdeal (dual (hStd E n) L) ↔
      ∀ y ∈ localization₂ (conjPrime₂ Q).asIdeal L, hStd E n y x ∈ localization₂ Q.asIdeal (1 : Submodule (𝓞 E) E) := by
  constructor
  · intro hx y hy
    obtain ⟨s, hs, hsx⟩ := (mem_locP Q _ x).1 hx
    obtain ⟨t, ht, hty⟩ := (mem_locP (conjPrime₂ Q) L y).1 hy
    rw [mem_conjP] at ht
    have h1 := (mem_dual L (s • x)).1 hsx (t • y) hty
    rw [hStd_osmul_left, smul_smul, hStd_osmul_right] at h1
    refine (mem_locP Q _ _).2 ⟨cO E t * s, ?_, h1⟩
    intro hm
    rcases Q.isPrime.mem_or_mem hm with h | h
    · exact ht h
    · exact hs h
  · intro H
    obtain ⟨S, hS⟩ := hL
    have H' : ∀ y ∈ S, ∃ s : 𝓞 E, s ∉ Q.asIdeal ∧ s • hStd E n y x ∈ (1 : Submodule (𝓞 E) E) := by
      intro y hy
      have hyL : y ∈ L := hS ▸ Submodule.subset_span hy
      exact (mem_locP Q _ _).1 (H y (Formalism.L2.DIV.lc_le_locP (conjPrime₂ Q) L hyL))
    choose f hf hfx using H'
    refine (mem_locP Q _ x).2 ⟨∏ y ∈ S.attach, f y.1 y.2, ?_, ?_⟩
    · intro hm
      obtain ⟨a, _, ha⟩ := (Q.isPrime.prod_mem_iff).1 hm
      exact hf a.1 a.2 ha
    · rw [mem_dual]
      intro y hy
      rw [← hS] at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        rw [hStd_osmul_right, ← Finset.prod_erase_mul S.attach (fun a => f a.1 a.2) (Finset.mem_attach S ⟨z, hz⟩),
          mul_smul]
        exact Submodule.smul_mem _ _ (hfx z hz)
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
      | smul r a _ ha =>
        rw [hStd_osmul_left, hStd_osmul_right]
        exact Submodule.smul_mem _ _ ha

theorem use₅ (Q : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n))
    (hA : Submodule.IsLattice E A) (hB : Submodule.IsLattice E B)
    (h : localization₂ (conjPrime₂ Q).asIdeal A = localization₂ (conjPrime₂ Q).asIdeal B) :
    localization₂ Q.asIdeal (dual (hStd E n) A) = localization₂ Q.asIdeal (dual (hStd E n) B) := by
  ext x
  rw [mem_localization_dual_iff Q A hA.fg, mem_localization_dual_iff Q B hB.fg, h]

end GlobalTheory.DualLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyIsoKG
section
open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators

namespace GlobalTheory.FourCopiesIso

theorem linearIndependent_of_orthogonal {K V J : Type} [Field K] [AddCommGroup V] [Module K V]
    (h : V → V →ₗ[K] K) (v : J → V) (h0 : ∀ i, h (v i) (v i) ≠ 0) (ho : ∀ i j, i ≠ j → h (v j) (v i) = 0) :
    LinearIndependent K v := by
  classical
  rw [linearIndependent_iff']
  intro s g hs j hj
  have := congrArg (h (v j)) hs
  rw [map_sum, map_zero, Finset.sum_eq_single j] at this
  · rw [map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (h0 j)
  · intro i _ hij
    rw [map_smul, ho i j hij, smul_zero]
  · intro e; exact absurd hj e

theorem nonempty_isoKG : ∀ (K E : Type) [Field K] [CharZero K] [Field E] [Algebra K E] [FiniteDimensional K E] (cj : E →+* E) (σ : K →+* K) (ι : Type) [Fintype ι], Fintype.card ι = Module.finrank K E → (∀ x, cj (algebraMap K E x) = algebraMap K E (σ x)) → (∀ y, cj (cj y) = y) → (∀ y, Algebra.trace K E (cj y) = σ (Algebra.trace K E y)) → (∀ y, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace K E (y * cj y) = (a : K)) → Nonempty (IsoKG K E cj ι) := by
  intro K E _ _ _ _ _ cj σ ι _ hcard hσ hcc htr hpos
  classical
  let h : E → E →ₗ[K] K := fun y => (Algebra.trace K E) ∘ₗ LinearMap.mulRight K (cj y)
  have hh : ∀ x y, h y x = Algebra.trace K E (x * cj y) := fun _ _ => rfl
  have hne : ∀ x, x ≠ 0 → h x x ≠ 0 := by
    intro x hx e
    obtain ⟨a, ha, h1⟩ := hpos x hx
    rw [hh, h1] at e
    exact ha.ne' (by exact_mod_cast e)
  obtain ⟨s, hs⟩ : (⊤ : Submodule K E).FG := Module.Finite.fg_top
  obtain ⟨n, v, h0, ho, hsp⟩ := GlobalTheory.FourCopies.exists_orthogonal_family h
    (fun x y e => by
      rw [hh] at e ⊢
      have := htr (x * cj y)
      rw [e, map_zero, map_mul, hcc, mul_comm] at this
      exact this)
    (fun x e => by
      by_contra hx
      exact hne x hx e) s
  have htop : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hs]; exact Submodule.span_le.2 (fun y hy => hsp y hy)
  have hli := linearIndependent_of_orthogonal h v (fun i => hne _ (h0 i)) ho
  have hn : Module.finrank K E = n := by
    simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli htop)
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq (hcard.trans hn)
  choose a ha hav using fun i => hpos (v i) (h0 i)
  choose A hA hA' using fun i => GlobalTheory.FourCopies.exists_similitude (a i) (ha i)
  let H : (Fin 4 → E) → (Fin 4 → E) →ₗ[K] K := fun y => ∑ k, h (y k) ∘ₗ LinearMap.proj k
  have hH : ∀ x y, H y x = ∑ k, Algebra.trace K E (x k * cj (y k)) := by
    intro x y
    simp only [H, LinearMap.sum_apply]
    rfl
  let b : Fin 4 × ι → (Fin 4 → E) := fun w k => (A (e w.2) w.1 k : E) * v (e w.2)
  have hb : ∀ w w', H (b w') (b w) = if w = w' then 1 else 0 := by
    intro w w'
    have h1 : H (b w') (b w) =
        ((∑ k, A (e w.2) w.1 k * A (e w'.2) w'.1 k : ℚ) : K) * h (v (e w'.2)) (v (e w.2)) := by
      rw [hH, hh]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← smul_eq_mul (_ * _ : K), ← map_smul, Algebra.smul_def]
      congr 1
      simp only [b, map_mul, map_ratCast]
      ring
    rw [h1]
    by_cases hi : w.2 = w'.2
    · rw [← hi, hh, hav, ← Rat.cast_mul, mul_comm, hA]
      have : w.1 = w'.1 ↔ w = w' := ⟨fun t => Prod.ext t hi, fun t => by rw [t]⟩
      simp only [this]
      split_ifs <;> simp
    · have : w ≠ w' := fun t => hi (by rw [t])
      rw [if_neg this, ho _ _ (fun t => hi (e.injective t)), mul_zero]
  have hbl : LinearIndependent K b :=
    linearIndependent_of_orthogonal H b (fun i => by rw [hb]; simp) (fun i j hij => by rw [hb, if_neg hij])
  have : Nonempty ι := by
    rw [← Fintype.card_pos_iff, hcard]; exact Module.finrank_pos
  have hc : Fintype.card (Fin 4 × ι) = Module.finrank K (Fin 4 → E) := by
    rw [Module.finrank_pi_fintype, Fintype.card_prod, hcard]; simp
  let B := basisOfLinearIndependentOfCardEqFinrank hbl hc
  have hB : ∀ w, B w = b w := fun w => by simp [B]
  have hco : ∀ x w, H (b w) x = B.equivFun x w := by
    intro x w
    conv_lhs => rw [← B.sum_equivFun x]
    simp only [map_sum, map_smul, hB, hb, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp
  refine ⟨⟨B.equivFun, fun x y => ?_⟩⟩
  have hy : ∀ k, cj (y k) = ∑ w, algebraMap K E (σ (B.equivFun y w)) * cj (b w k) := by
    intro k
    conv_lhs => rw [← B.sum_equivFun y]
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, hB]
    simp only [Algebra.smul_def, map_mul, hσ]
  simp only [hσ, ← map_mul, ← map_sum]
  congr 1
  simp only [hy, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← hco x w, hH, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, ← smul_eq_mul (σ _), ← map_smul, Algebra.smul_def]
  congr 1
  ring

end GlobalTheory.FourCopiesIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquarefreePrimeSumExceptionalStatement
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefree_prime_sum_exceptional : GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ m₀ a₀ : ℕ, 8 ∣ m₀ → 0 < m₀ → Nat.Coprime a₀ m₀ → ∀ X : ℝ, 0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X → ∃ nStar : ℕ, ∀ s : ℕ, 1 < s → Squarefree s → Nat.Coprime s m₀ → (s : ℝ) ≤ x ^ (800 : ℝ) → s ≠ nStar → |(∑ p ∈ Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X, (jacobiSym (p : ℤ) s : ℝ)) / (Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X).card| ≤ C' * Real.exp (-c' * Real.log x ^ 2) := by
  first | exact @GlobalTheory.Mem.An.jacobi_mean_small | exact GlobalTheory.Mem.An.jacobi_mean_small | (intros; apply GlobalTheory.Mem.An.jacobi_mean_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScale
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol.ScaleExists

theorem trueScale_isScale : ∀ cd : CDHaar, CdScaleIs cd (trueScale cd) :=
  GlobalTheory.Mem.Vol.Scale.cdScaleIs_trueScale

end GlobalTheory.Mem.Vol.ScaleExists
end

