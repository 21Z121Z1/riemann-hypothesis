import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanLiftTraceFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupActsByLiftTranslationPrincipalType
section
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.PhaseRational

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem eq_of_out {V : HSp D} {F F' : GA D V → ℂ} (hF : ∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g)
    (hF' : ∀ γ ∈ GQ V, ∀ g, F' (γ * g) = F' g) (h : ∀ q : AutQ V, F q.out = F' q.out) (g : GA D V) : F g = F' g := by
  let q : AutQ V := Quotient.mk _ g
  have hq : (QuotientGroup.rightRel (GQ V)) g q.out := (QuotientGroup.rightRel (GQ V)).iseqv.symm (Quotient.exact (Quotient.out_eq q))
  rw [QuotientGroup.rightRel_apply] at hq
  have e : q.out = (q.out * g⁻¹) * g := by group
  have h1 := h q
  rw [e, hF _ hq, hF' _ hq] at h1
  exact h1

theorem mult_leftInv {V : HSp D} {S : D.what₂.Tau → SPar} {θ} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {T : MMap M} (hT : T ∈ Mult.Mult θ M J χ) (v : M.Vec) : ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  intro γ hγ g
  induction hT using Submodule.span_induction with
  | mem T h => exact (h.aut v).toIsAutFun.1 γ hγ g
  | zero => rfl
  | add T T' _ _ h h' => simp [h, h']
  | smul c T _ h => simp [h]

theorem adel_muPin_leftInv {C : Core D} (hL : LawsM C) {j : ℕ} (hj : InR D j) {σ : C.Q.c.F →+* ℂ} (hσ : GoodEmb C.Q.c σ)
    {W : HSp D} (hV : C.V j σ = W) (cc : (C.U j σ).Comp → ℂ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n)
    {f : C.R j} (hf : f ∈ sec (C.Q.Xo j) C.Q.c a n) : ∀ γ ∈ GQ W, ∀ g,
    adel W (castDict hV (C.dict j σ)) (muPin W (castDict hV (C.dict j σ)) (castDict hV (C.mu j σ)) cc) (rdU (C.U j σ) f) (γ * g) =
    adel W (castDict hV (C.dict j σ)) (muPin W (castDict hV (C.dict j σ)) (castDict hV (C.mu j σ)) cc) (rdU (C.U j σ) f) g := by
  subst hV
  intro γ hγ g
  obtain ⟨th, hr, -, hD⟩ := hL.dictU j hj σ hσ
  have h1 := rdU_leftInv (C.U j σ) (C.V j σ) (C.dict j σ) (C.mu j σ) (C.Kf j σ) th hr (hL.unf j hj σ hσ) hD
    (hL.muUnit j hj σ hσ) hd (hL.chiTriv j hj σ hσ a n hd) hf γ hγ g
  obtain ⟨γ', -, he⟩ := hD.1 γ hγ g
  have h2 : (C.dict j σ (γ * g)).1 = (C.dict j σ g).1 := by rw [he]
  show cc (C.dict j σ (γ * g)).1 * C.mu j σ (γ * g) * _ = cc (C.dict j σ g).1 * C.mu j σ g * _
  rw [mul_assoc, mul_assoc]
  exact congrArg₂ (· * ·) (congrArg cc h2) h1

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem finiteGroup_acts_by_lift_translation_principalType {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (g : G)
    (hg : ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) :
    ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k ∧ ∀ F h,
      Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F h = F (h * k) := by
  refine ⟨hg.choose, hg.choose_spec, fun F h => ?_⟩
  have h1 : Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) hg.choose = 1 := by
    unfold Lev.levChi levFn
    have : ext1 (Lev.flagL (R.datWp i R.triv)).P.H (Lev.flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (Lev.flagL (R.datWp i R.triv)) (Lev.finE (Wc D i) hg.choose)) = 1 := Lev.subgroupCharExtension_one_apply _ _
    rw [this]
    simp [Lev.flagL, Lev.withP, LevCh.datWp, Lev.datY]
  show Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F h = _
  unfold Lev.actG0
  rw [dif_pos hg]
  simp only [h1, inv_one, one_mul]

theorem rdU_of_isBC {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l}
    (hle : c.F ≤ c'.F) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) {m : ℕ} {f' : Rul Xo c'}
    {as : Fin m → c'.F} {fs : Fin m → Rul Xo c} (h : IsBC hle f' as fs) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (x : Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) :
    rdU (unfBC hle U σ') f' k x = ∑ i, σ' (as i) * rdU (U (σ'.comp (incF c c' hle))) (fs i) k x := by
  classical
  by_cases hx : x ∈ ((U (σ'.comp (incF c c' hle))).X k).dom
  · let _ : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
    have h1 := h (CAt σ') (fun _ => rfl) ((unfBC hle U σ').un k ⟨x, hx⟩)
    have e1 : rdU (unfBC hle U σ') f' k x = toC (evR Xo c' f' ((unfBC hle U σ').un k ⟨x, hx⟩)) := dif_pos hx
    have e2 : ∀ i, rdU (U (σ'.comp (incF c c' hle))) (fs i) k x =
      toC (evR Xo c (fs i) ((U (σ'.comp (incF c c' hle))).un k ⟨x, hx⟩)) := fun i => dif_pos hx
    simp only [e2]
    rw [e1]
    exact h1
  · have e1 : rdU (unfBC hle U σ') f' k x = 0 := dif_neg hx
    have e2 : ∀ i, rdU (U (σ'.comp (incF c c' hle))) (fs i) k x = 0 := fun i => dif_neg hx
    simp only [e2, e1, mul_zero, Finset.sum_const_zero]

theorem row_baseChange {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l}
    (hle : c.F ≤ c'.F) {r n : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (V : HSp D)
    (dict : GA D V → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {Γ : Type} [Group Γ]
    (lev : Γ → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (hL : ActLev (Xo := Xo) c lev)
    {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs] {Tup : Type} {dδ : Tup → DeltaDat Xo c' n}
    {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
    {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F} {La : ∀ t, Cl' t → GenLat D.host.E n} {Nc : ∀ t, Cl' t → ℕ}
    {gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F} {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
    {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {LL : IntermediateField ℚ ℂ}
    {cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ} {ph : ℂ}
    (hrow : OneMapRow Xo c' V (unfBC hle U σ') dict mu xr a (actLev c' lev) dδ Cl' w La Nc gam vol ep io thAd Pl LL
      (cusp Xo c' (unfBC hle U) a n) cc ph) (t : Tup) (x : Cl' t → Vs) (hx : Pl t x) :
    ∃ (z : Γ) (ze : ℂ) (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), ze ∈ LL ∧ (∀ k, fs k ∈ cusp Xo c U a n) ∧
      ∀ q : AutQ V, ph * thAd t x q = ∑ k, ze * σ' (as k) * ((lieFac Dw xr a : ℂ) *
        adel V dict (muPin V dict mu cc) (rdU (U (σ'.comp (incF c c' hle))) (actLev c lev z (fs k))) q.out) := by
  obtain ⟨-, -, z, -, hrow⟩ := hrow
  obtain ⟨ze, hze, -, hrow⟩ := hrow t
  obtain ⟨⟨f', hf', hcl⟩, hall⟩ := hrow x hx
  have hf's := cusp_le_sec _ _ _ _ _ hf'
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC D.host.E H Dw l Xo c c' hle).2 r U a n f' hf'
  have hBCz := (GlobalTheory.FieldBC.actLev_and_actBC D H Dw l Xo c c' hle Γ lev hL).2 a n z m as fs f' hf's
    (fun k => cusp_le_sec _ _ _ _ _ (hfs k)) hBC
  refine ⟨z, ze, m, as, fs, hze, hfs, fun q => ?_⟩
  have h1 := hall f' hf's hcl q
  have h2 := rdU_of_isBC hle U σ' hBCz (dict q.out).1 (dict q.out).2
  have h3 : jFn V σ' (rdU (unfBC hle U σ')) dict mu (actLev c' lev z f') q = mu q.out * ∑ k, σ' (as k) *
      rdU (U (σ'.comp (incF c c' hle))) (actLev c lev z (fs k)) (dict q.out).1 (dict q.out).2 :=
    congrArg (mu q.out * ·) h2
  rw [h1, h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [adel_muPin]
  change ze * cc (dict q.out).1 * _ * _ = _
  ring

theorem placed_of_pins {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
    {K' : Type} [Field K'] {σ' : K' →+* ℂ} {t : T0} {v₀ : (R.MW i (sg0 D A)).Vec} {c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W}
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {bad : ℕ} {Mb I : Ideal (𝓞 D.host.E)} {N : Submodule (𝓞 D.host.E) La} {Cl : Type} [Fintype Cl]
    {Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)} {gam : Cl → ℕ} {vol : K'}
    {B : Ideal (𝓞 D.host.E) → K'} {xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ}
    {φ : (Fin (Vc D i).rank → La ⧸ N) → K'} {thAd : (Cl → VsV D i K') → AutQ (Wc D i) → ℂ}
    {Plc : (Cl → VsV D i K') → Prop} (h : ThPinsT R i σ' t v₀ c0' ι bad Mb I N Lh gam vol B xi φ thAd Plc)
    (x : A.fam.amb.FL i t) : ∃ y, Plc y ∧ ∀ q, thAd y q = R.thF i t (jVx R i t x) v₀ q.out :=
  h.reps.elim fun _ h => h.elim fun _ h => (h.2.1 x).imp fun y hy =>
    ⟨(h.2.2.2 y).2 ⟨x, hy⟩, fun q => congrFun (h.2.2.1 _ y hy) q⟩

theorem comb_fin {K M X ι : Type} [Fintype ι] (e : K → ℂ) (P : M → X → ℂ) (F : X → ℂ) (a : ι → K) (f : ι → M)
    (h : ∀ x, F x = ∑ k, e (a k) * P (f k) x) :
    ∃ (n : ℕ) (a : Fin n → K) (f : Fin n → M), ∀ x, F x = ∑ k, e (a k) * P (f k) x :=
  ⟨Fintype.card ι, fun k => a ((Fintype.equivFin ι).symm k), fun k => f ((Fintype.equivFin ι).symm k), fun x =>
    (h x).trans ((Fintype.equivFin ι).symm.sum_comp fun k => e (a k) * P (f k) x).symm⟩

section Main

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

abbrev IdentityAt (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  OneMapRow (C.Q.Xo ((i : ℕ) + 1)) O.c' (Wc D i)
    (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (xiR D) (wtA κ)
    (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io
    O.thAd O.Plc D.what₂.embLL.toRatAlgHom.fieldRange
    (cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank) cc ph

theorem lift_rational (v₀ : (R.MW i (sg0 D A)).Vec) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ)
    {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
    (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (hpins : O.Pins κ v₀ ι x₀)
    (hlaws : LawsM C) (hn : κ.n = D.R.nV) (hmem : R.thP_thF_mem)
    (hequiv : O.EquivAt κ cc) (hid : IdentityAt O κ cc ph) (t : Tp) (t₀ : T0) (ht : tup t = t₀)
    (x : A.fam.amb.FL i t₀) :
    ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), ∀ h,
      ph * R.thF i t₀ (jVx R i t₀ x) v₀ h =
        ∑ k, D.what₂.embLL (a k) * ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi cc (f k : C.R ((i : ℕ) + 1)) h) := by
  revert x
  refine ht.rec fun x => ?_
  have hrk : (Vc D i).rank = κ.n := (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).trans hn.symm
  refine (placed_of_pins (hpins.tuple t) x).elim fun y hy => ?_
  refine (row_baseChange O.hle (C.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu
    (xiR D) (wtA κ) O.lev2 hpins.act.1 hid t y hy.1).elim fun z h => h.elim fun ze h => h.elim fun m h => h.elim fun as h =>
      h.elim fun fs h => h.1.elim fun ze' hze' => (hpins.lift.lev z).elim fun kz hkz => ?_
  have hz : ∀ k, actLev C.Q.c O.lev2 z (fs k) ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n := fun k =>
    (hequiv z kz hkz.1 (fs k) (hrk ▸ h.2.1 k)).1
  have has : ∀ k, ∃ b : D.what₂.LL, D.what₂.embLL b = inC O.c' (as k) := fun k => hF.le (as k).2
  refine ⟨m, fun k => ze' * (has k).choose, fun k => ⟨_, hz k⟩, ?_⟩
  refine eq_of_out (V := Wc D i) (fun γ hγ g => ?_) (fun γ hγ g => ?_) fun q => ?_
  · exact congrArg (ph * ·) (mult_leftInv (hmem i (tup t) _) v₀ γ hγ g)
  · refine Finset.sum_congr rfl fun k _ => congrArg (_ * ·) (congrArg (_ * ·) ?_)
    exact adel_muPin_leftInv hlaws ⟨Nat.le_add_left _ _, i.2⟩ (σ := O.s0) C.good_σ₀ O.hV cc (dom_wtA κ)
      (cusp_le_sec _ _ _ _ _ (hz k)) γ hγ g
  · refine (congrArg (ph * ·) (hy.2 q)).symm.trans ((h.2.2 q).trans ?_)
    refine Finset.sum_congr rfl fun k _ => congrArg (· * _) ?_
    exact (congrArg₂ (· * ·) hze' (has k).choose_spec).symm.trans (map_mul D.what₂.embLL _ _).symm

theorem proj_rational (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (s ph : ℂ)
    (hlift : ∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) (hchi : R.grp_chiW)
    (hequiv : O.EquivAt κ cc) (F : GA D (Wc D i) → ℂ) (n : ℕ) (a : Fin n → D.what₂.LL)
    (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n)
    (hF : ∀ h, ph * F h = ∑ k, D.what₂.embLL (a k) * (s * O.phi cc (f k : C.R ((i : ℕ) + 1)) h)) :
    ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), ∀ h,
      ph * R.eWf i (sg0 D A) F h = ∑ k, D.what₂.embLL (a k) * (s * O.phi cc (f k : C.R ((i : ℕ) + 1)) h) := by
  have hact := fun g => finiteGroup_acts_by_lift_translation_principalType R i g (hlift g)
  have heq := fun g (k : Fin n) => hequiv g _ (hact g).choose_spec.1 _ (f k).2
  refine comb_fin D.what₂.embLL
    (fun (u : C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) h => s * O.phi cc (u : C.R ((i : ℕ) + 1)) h)
    (fun h => ph * R.eWf i (sg0 D A) F h)
    (fun p : G × Fin n => (idemOf A.X).coeff p.1 * ((((R.FW i).chi p.1)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) * a p.2)
    (fun p => ⟨_, (heq p.1 p.2).1⟩) fun h => ?_
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have h1 : R.eWf i (sg0 D A) F h = ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) * F (h * (hact g).choose) := by
    unfold RealDat.eWf gaL
    rw [LinearMap.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← (hact g).choose_spec.2 F h, ← hs]
    rfl
  rw [h1, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_left_comm, hF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 := ((heq g k).2 h).trans (congrArg (· * _) (hchi i g).symm)
  have h3 : D.what₂.embLL ((((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) *
      D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  dsimp only
  rw [h2, map_mul, map_mul]
  linear_combination (-(D.what₂.embLL ((idemOf A.X).coeff g) * D.what₂.embLL (a k) * s *
    O.phi cc (f k : C.R ((i : ℕ) + 1)) (h * (hact g).choose))) * h3

theorem phRat_of_identity (v₀ : (R.MW i (sg0 D A)).Vec) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ)
    {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ} (t : Tp) (ht : tup t = A.μ0)
    (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (hpins : O.Pins κ v₀ ι x₀)
    (hlaws : LawsM C) (hn : κ.n = D.R.nV) (hchi : R.grp_chiW) (hmem : R.thP_thF_mem) (hG : R.thP_thG)
    (hequiv : O.EquivAt κ cc) (hid : IdentityAt O κ cc ph) : O.PhRat κ v₀ cc ph := by
  have key := lift_rational O κ v₀ cc ph hF hpins hlaws hn hmem hequiv hid t A.μ0 ht
  intro x
  refine (key x).elim fun n h => h.elim fun a h => h.elim fun f h => ?_
  have h1 := proj_rational O κ cc _ ph (fun g => (hpins.lift.lev g).imp fun _ hk => hk.1) hchi hequiv _ n a f h
  refine h1.imp fun _ h2 => h2.imp fun _ h2 => h2.imp fun _ h2 g => Eq.trans (congrArg (ph * ·) ?_) (h2 g)
  exact congrArg (fun S : MMap (R.MW i (sg0 D A)) => S v₀ g) (hG i A.μ0 (jVx R i A.μ0 x))

end Main

section Class

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m)

end Class

end GlobalTheory.PhaseRational
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlParabolicOrbitRepresentatives
section
open Matrix

namespace GlobalTheory.OrbitsGLParab

variable {k : Type} [Field k]

variable {n m : ℕ}

def cols (X : Matrix (Fin n) (Fin m) k) : Fin m → Fin n → k := fun j r => X r j

theorem exists_coeff (X : Matrix (Fin n) (Fin m) k) (j : Fin m)
    (hj : cols X j ∈ Submodule.span k (cols X '' Set.Ioi j)) :
    ∃ c : Fin m → k, (∀ i, ¬ j < i → c i = 0) ∧ ∀ r, ∑ i, c i * X r i = X r j := by
  obtain ⟨l, hl, hx⟩ := (Finsupp.mem_span_image_iff_linearCombination k).1 hj
  refine ⟨l, fun i hi => ?_, fun r => ?_⟩
  · by_contra h
    exact hi (hl (Finsupp.mem_support_iff.2 h))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hx
    have := congrFun hx r
    simpa [Finset.sum_apply, cols] using this

open Classical in

noncomputable def coef (X : Matrix (Fin n) (Fin m) k) : Matrix (Fin m) (Fin m) k :=
  Matrix.of fun i j => if h : cols X j ∈ Submodule.span k (cols X '' Set.Ioi j) then
    (exists_coeff X j h).choose i else 0

theorem coef_of_not_mem (X : Matrix (Fin n) (Fin m) k) {j : Fin m}
    (hj : cols X j ∉ Submodule.span k (cols X '' Set.Ioi j)) (i : Fin m) : coef X i j = 0 := by
  unfold coef
  simp [hj]

theorem sum_coef (X : Matrix (Fin n) (Fin m) k) {j : Fin m}
    (hj : cols X j ∈ Submodule.span k (cols X '' Set.Ioi j)) (r : Fin n) :
    ∑ i, X r i * coef X i j = X r j := by
  unfold coef
  simp only [of_apply, dif_pos hj]
  rw [← (exists_coeff X j hj).choose_spec.2 r]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

noncomputable def clr (X : Matrix (Fin n) (Fin m) k) : Matrix (Fin m) (Fin m) k := 1 - coef X

open Classical in
theorem mul_clr (X : Matrix (Fin n) (Fin m) k) (r : Fin n) (j : Fin m) :
    (X * clr X) r j = if cols X j ∈ Submodule.span k (cols X '' Set.Ioi j) then 0 else X r j := by
  rw [clr, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, mul_apply]
  split_ifs with hj
  · rw [sum_coef X hj, sub_self]
  · simp [coef_of_not_mem X hj]

theorem linInd (X : Matrix (Fin n) (Fin m) k) :
    LinearIndependent k
      (fun j : {j : Fin m // cols X j ∉ Submodule.span k (cols X '' Set.Ioi j)} => cols X j.1) := by
  classical
  rw [linearIndependent_iff']
  intro s g hs i hi
  by_contra hne
  set T := s.filter (fun i => g i ≠ 0) with hTdef
  have hT : T.Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, hne⟩⟩
  set j := T.min' hT with hjdef
  have hjT : j ∈ T := T.min'_mem hT
  obtain ⟨hjs, hgj⟩ := Finset.mem_filter.1 hjT
  apply j.2
  have key : g j • cols X j.1 = - ∑ i ∈ s.erase j, g i • cols X i.1 := by
    rw [← Finset.add_sum_erase s _ hjs] at hs
    exact eq_neg_of_add_eq_zero_left hs
  have hmem : ∑ i ∈ s.erase j, g i • cols X i.1 ∈ Submodule.span k (cols X '' Set.Ioi j.1) := by
    refine Submodule.sum_mem _ fun i hi => ?_
    by_cases hgi : g i = 0
    · simp [hgi]
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.1, ?_, rfl⟩)
      have hiT : i ∈ T := Finset.mem_filter.2 ⟨Finset.mem_of_mem_erase hi, hgi⟩
      have hle : j ≤ i := T.min'_le i hiT
      have hne : i ≠ j := Finset.ne_of_mem_erase hi
      exact (lt_of_le_of_ne hle (Ne.symm hne) : j < i)
  have : cols X j.1 = (g j)⁻¹ • (g j • cols X j.1) := by rw [smul_smul, inv_mul_cancel₀ hgj, one_smul]
  rw [this, key]
  exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hmem)

theorem exists_decomp (X : Matrix (Fin n) (Fin m) k) :
    ∃ (g : GL (Fin n) k) (s : Matrix (Fin n) (Fin m) k), (∀ i j, s i j = 0 ∨ s i j = 1) ∧
      X * clr X = (g : Matrix (Fin n) (Fin n) k) * s := by
  classical
  have hli := linInd X
  let B := Module.Basis.sumExtend hli
  have hB : ∀ j, B (Sum.inl j) = cols X j.1 := by
    intro j
    simp only [B, Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend,
      Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply]
    rfl
  let e := B.indexEquiv (Pi.basisFun k (Fin n))
  let b := B.reindex e
  have hb : ∀ j, b (e (Sum.inl j)) = cols X j.1 := by
    intro j
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, hB]
  let G : Matrix (Fin n) (Fin n) k := Matrix.of fun r l => b l r
  have hG : G = (Pi.basisFun k (Fin n)).toMatrix b := by
    ext r l
    simp [G, Module.Basis.toMatrix_apply]
  have hdet : G.det ≠ 0 := by
    rw [hG]
    have := (Pi.basisFun k (Fin n)).invertibleToMatrix b
    exact (isUnit_det_of_invertible _).ne_zero
  let s : Matrix (Fin n) (Fin m) k := Matrix.of fun r j =>
    if h : cols X j ∈ Submodule.span k (cols X '' Set.Ioi j) then 0
    else if r = e (Sum.inl ⟨j, h⟩) then 1 else 0
  refine ⟨GeneralLinearGroup.mkOfDetNeZero G hdet, s, fun i j => ?_, ?_⟩
  · simp only [s, of_apply]
    split_ifs <;> simp
  · ext r j
    rw [mul_clr, GeneralLinearGroup.val_mkOfDetNeZero, mul_apply]
    simp only [s, of_apply]
    split_ifs with hj
    · simp
    · rw [Finset.sum_eq_single (e (Sum.inl ⟨j, hj⟩))]
      · have := congrFun (hb ⟨j, hj⟩) r
        simp only [G, of_apply, if_pos rfl, mul_one, dif_neg hj]
        rw [this]
        simp [cols]
      · intro l _ hl
        simp [hl, dif_neg hj]
      · simp

end GlobalTheory.OrbitsGLParab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricLocalTransgressionFormula
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mem_offHyp_iff {n : ℕ} {S : Finset (Fin n)}
    {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n} :
    v ∈ _root_.GlobalTheory.GoodTop.offHyp S U ↔ v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0 := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  exact Iff.rfl

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mixTop_slot_smul_sub_sub {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] (A B D : _root_.GlobalTheory.GoodTop.EndValuedForm11Coeffs n r) (s : ℂ) (j : Fin n) :
    _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A (s • (A - B) - D) B j) =
      s * _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A (A - B) B j) +
        (-1) * _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A D B j) := by
  rw [← _root_.GlobalTheory.GoodTop.mixTop_position_linear, neg_one_smul, ← sub_eq_add_neg]

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in

theorem _root_.GlobalTheory.GoodTop.integral_cutTop_sub : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a i j, ‖_root_.GlobalTheory.HermFrame.conn G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ * _root_.GlobalTheory.GoodMetric.poinWt S v a ≤ c) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a b i j, ‖_root_.GlobalTheory.HermFrame.curv G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ * (_root_.GlobalTheory.GoodMetric.poinWt S v a * _root_.GlobalTheory.GoodMetric.poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) - (∫ v in U, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) = ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hS hG₀ hG₁ hconn hcurv hρ hρK
  have hstokes := _root_.GlobalTheory.GoodTop.integral_mixTop_position_eq_zero S U K G₀ G₁ ρ c hU hK hKU
    hS hG₀ hG₁ hconn hcurv hρ hρK
  have hF₁ := _root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt S U K G₀ G₁ ρ c hU hK hKU hS
    hG₀ hG₁ hconn hcurv hρ hρK
  have hF₀ := (_root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth U K G₀ ρ hU hK hKU hG₀ hρ
    hρK).mono_set (fun v hv => ((mem_offHyp_iff (S := S)).1 hv).1)
  have hT := _root_.GlobalTheory.GoodTop.integrableOn_corrC S U K G₀ G₁ ρ c hU hK hKU hS
    hG₀ hG₁ hconn hcurv hρ hρK
  have hpt : ∀ v, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v =
      ∑ j, _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ v)
        ((ρ v : ℂ) • (_root_.GlobalTheory.GoodTop.curvAt G₁ v - _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
          _root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ v) (_root_.GlobalTheory.GoodTop.curvAt G₀ v) j) := by
    intro v
    simp_rw [mixTop_slot_smul_sub_sub]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      _root_.GlobalTheory.GoodTop.sum_mixTop_position_sub]
    unfold _root_.GlobalTheory.GoodTop.corrC
    ring
  have hzero : ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
      ((ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v) = 0 := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_finset_sum _ fun j _ => (hstokes j).1]
    exact Finset.sum_eq_zero fun j _ => (hstokes j).2
  have hsplit : ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
      ((ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v) =
      (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v := by
    have hsub : IntegrableOn (fun v =>
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v))
        (_root_.GlobalTheory.GoodTop.offHyp S U) := hF₁.sub hF₀
    exact (integral_sub hsub hT).trans (congrArg (· - _) (integral_sub hF₁ hF₀))
  rw [← setIntegral_congr_set (_root_.GlobalTheory.GoodTop.offHyp_ae_eq S U)]
  linear_combination hzero - hsplit

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanLiftTraceFormulaStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDeriv_archimedeanLift_traceFormula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) ≃L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ), ∀ (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ∀ f ∈ schA F (Fin n × Fin d), heisD M ψ (liftI M ζ) f = dR F (T : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (-(2 * Real.pi * Complex.I)) ζ f := by
  first | exact @GlobalTheory.ArchDecay.HeisArch.heisD_liftI | exact GlobalTheory.ArchDecay.HeisArch.heisD_liftI | (intros; apply GlobalTheory.ArchDecay.HeisArch.heisD_liftI <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivArchimedeanWeilRepIntertwineStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDeriv_archimedean_weilRep_intertwine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evI F) u → ∀ f ∈ schA F (Fin n × Fin d), heisD M B.ψ u (om p f) = om p (heisD M B.ψ (actAB (cA σ) p⁻¹ u) f) := by
  first | exact @GlobalTheory.ArchDecay.HeisWeil.heisD_weil | exact GlobalTheory.ArchDecay.HeisWeil.heisD_weil | (intros; apply GlobalTheory.ArchDecay.HeisWeil.heisD_weil <;> assumption)
end

