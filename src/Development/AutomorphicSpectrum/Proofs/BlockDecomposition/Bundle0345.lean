import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0002
import BuildAid.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerMuGaloisCompat
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.MuGal

theorem mu_gal {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (t : Mid.HM r M n j) :
    B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j (Mid.mu r M n j hT t) = Mid.mu r M n j hT (galM r M σ hσ n j t) := by
  unfold B.galHc Mid.mu galM B.galMorC Mid.muMor galT'
  symm
  exact cr_square
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (gal_κm r σ hσ n)) fun _ _ _ => rfl)
    (Mid.mIn r M n hT)
    (Mid.mIn r M n hT)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (B.gal_κb (okToOC l K) σ (galOC_okToOC σ) true n)) fun _ _ _ => rfl)
    (galBase_cris σ n) (fun _ => rfl) (fun _ => rfl) (galBase_cris σ n) (fun _ => rfl)
    (fun _ _ => rfl) j t

end GlobalTheory.CompanionTheory.MuGal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerMuReductionCompat
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrysMid

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

noncomputable def trueRed (M : Model l K) (n : ℕ) :
    Mor (B.Lc (B.schFn M.p) (okToOC l K) true (n + 1)) (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).red (Nat.le_succ n)) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true (n + 1)) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).red (Nat.le_succ n)) rfl (B.dd_red true _ (Nat.le_succ n))
      (B.basePt _ _ (B.red_κb (okToOC l K) true (Nat.le_succ n))) fun _ _ _ => rfl

noncomputable def midRed (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n : ℕ) :
    Mor (Mid.Lm r M (n + 1)) (Mid.Lm r M n) ((base l).red (Nat.le_succ n)) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true (n + 1)) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).red (Nat.le_succ n)) rfl (B.dd_red true _ (Nat.le_succ n))
      (B.basePt _ _ (red_κm r (Nat.le_succ n))) fun _ _ _ => rfl

theorem ptIn_val (F : B.Fn (OK l K)) {r : CrystallineSemistableComparison.Res l K} {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (F.ptK (B.κb (okToOC l K) true n)).obj B₀) (h : (l : B₀) = 0) :
    ((Mid.ptIn F n hT).app B₀ y).1.2 = F.Pt.map (CommRingCat.ofHom (Mid.frbN h N)) y.1.2 := rfl

theorem base_val {O : Type} [CommRing O] (F : B.Fn O) {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {κ₁ : O →+* k₁} {κ₂ : O →+* k₂}
    (τ : k₁ →+* k₂) (h : τ.comp κ₁ = κ₂) (B₀ : CommRingCat.{0}) (y : (F.ptK κ₂).obj B₀) :
    ((B.basePt F τ h).app B₀ y).1.2 = y.1.2 := rfl

theorem ptIn_base (F : B.Fn (OK l K)) (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (F.ptK (B.κb (okToOC l K) true n)).obj B₀) :
    ((Mid.ptIn F (n + 1) hT).app B₀ ((B.basePt F _ (B.red_κb (okToOC l K) true (Nat.le_succ n))).app B₀ y)).1.2 =
      ((B.basePt F _ (red_κm r (Nat.le_succ n))).app B₀ ((Mid.ptIn F n hT).app B₀ y)).1.2 := by
  have h : (l : B₀) = 0 := Mid.l_zero y.1.1
  rw [ptIn_val F hT (n + 1) B₀ _ h, base_val, base_val, ptIn_val F hT n B₀ _ h]

theorem pt_sq (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (B.Lc (B.schFn M.p) (okToOC l K) true n).Pt.obj B₀) :
    ((Mid.mIn r M (n + 1) hT).pt.app B₀ ((trueRed M n).pt.app B₀ y)).1.2 =
      ((midRed r M n).pt.app B₀ ((Mid.mIn r M n hT).pt.app B₀ y)).1.2 :=
  ptIn_base (B.schFn M.p) r hT n B₀ y

theorem mid_square (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j) :
    (B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris n) (trueRed M n) (RingHom.id _) (B.red_cris _ (Nat.le_succ n))).pull j
      ((B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris (n + 1)) (Mid.mIn r M (n + 1) hT) (RingHom.id _) (Wc.idc _)).pull j t) =
    (B.omMor (c := (base l).cris n) (c' := (base l).cris n) (Mid.mIn r M n hT) (RingHom.id _) (Wc.idc _)).pull j
      ((B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris n) (midRed r M n) (RingHom.id _) (B.red_cris _ (Nat.le_succ n))).pull j t) :=
  cr_square (F₁ := B.schFn M.p) (F₂ := B.schFn M.p) (F₃ := B.schFn M.p) (F₄ := B.schFn M.p)
    (b₁ := B.bs l true (n + 1)) (b₂ := B.bs l true (n + 1)) (b₃ := B.bs l true n) (b₄ := B.bs l true n)
    (h₁ := rfl) (h₂ := rfl) (h₃ := rfl) (h₄ := rfl)
    (κ₁ := Mid.κm r (n + 1)) (κ₂ := B.κb (okToOC l K) true (n + 1)) (κ₃ := Mid.κm r n) (κ₄ := B.κb (okToOC l K) true n)
    (Λ := Acris l) (c₁ := (base l).cris (n + 1)) (c₂ := (base l).cris (n + 1)) (c₃ := (base l).cris n)
    (c₄ := (base l).cris n) (τ := RingHom.id _)
    (Mid.mIn r M (n + 1) hT) (trueRed M n) (midRed r M n) (Mid.mIn r M n hT)
    (Wc.idc _) (B.red_cris _ (Nat.le_succ n)) (B.red_cris _ (Nat.le_succ n)) (Wc.idc _) (fun x => (Wc.idc ((base l).red (Nat.le_succ n)) x).symm)
    (pt_sq r hT M n) j t

theorem mu_redHc (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j) :
    B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j (Mid.mu r M (n + 1) j hT t) = Mid.mu r M n j hT ((redT r M (Nat.le_succ n)).pull j t) :=
  mid_square r hT M n j t

end GlobalTheory.CompanionTheory.CrysMid
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuGaloisCompat
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NuGalSquare

theorem cr_square_semi {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1}
    {h₃ : b₃.t = 1} {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I}
    {κ₄ : O →+* b₄.R ⧸ b₄.I} {Λ : Type} [CommRing Λ] {c₁ : Λ →+* b₁.R} {c₂ : Λ →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τa τb τc τd : Λ →+* Λ}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τa a)) (hb : ∀ a, σb (c₂ a) = c₄ (τb a)) (hc : ∀ a, σc (c₁ a) = c₃ (τc a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τd a)) (hτ : τb.comp τa = τd.comp τc) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb τb hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τa ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τd hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc τc hc).pull j x) := by
  haveI t₁ : RingHomCompTriple τa τb (τb.comp τa) := ⟨rfl⟩
  haveI t₂ : RingHomCompTriple τc τd (τb.comp τa) := ⟨hτ.symm⟩
  rw [pull_pull (τb.comp τa), pull_pull (τb.comp τa)]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem commute_phi_gal (σ : Gal(PadicAlgCl l/K)) : Commute (ACris.phi ℂ_[l] l) (ACris.galCris σ) :=
  RingHom.ext fun a => ACris.phi_gal_smul σ a

theorem phiA_comp_gal (σ : Gal(PadicAlgCl l/K)) (N : ℕ) :
    (Mid.phiA l N).comp (ACris.galCris σ) = (ACris.galCris σ).comp (Mid.phiA l N) :=
  ((commute_phi_gal σ).pow_left N).eq

theorem commute_phi_galBase (σ : Gal(PadicAlgCl l/K)) (n : ℕ) : Commute ((base l).phi n) (galBase σ n) :=
  RingHom.ext fun r => by
    obtain ⟨a, rfl⟩ := (RL.base_acr (base l) isBase_base).2 n |>.1 r
    change (base l).phi n (galBase σ n ((base l).cris n a)) = galBase σ n ((base l).phi n ((base l).cris n a))
    rw [galBase_cris, (base l).phi_cris, (base l).phi_cris, galBase_cris]
    exact congrArg _ (ACris.phi_gal_smul σ a)

theorem phiP_galBase (σ : Gal(PadicAlgCl l/K)) (n N : ℕ) (x : (base l).Acr n) :
    Mid.phiP l n N (galBase σ n x) = galBase σ n (Mid.phiP l n N x) :=
  RingHom.congr_fun ((commute_phi_galBase σ n).pow_left N).eq x

theorem nu_gal : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j), Mid.nu r M n j hT (B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j x) = galM r M σ hσ n j (Mid.nu r M n j hT x) := by
  intro l _ K r N hT M σ hσ n j x
  exact cr_square_semi
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (B.gal_κb (okToOC l K) σ (galOC_okToOC σ) true n)) fun _ _ _ => rfl)
    (Mid.mOut r M n hT) (Mid.mOut r M n hT)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (gal_κm r σ hσ n)) fun _ _ _ => rfl)
    (galBase_cris σ n) (Mid.phiP_cris n N) (Mid.phiP_cris n N) (galBase_cris σ n)
    (phiA_comp_gal σ N) (phiP_galBase σ n N) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.NuGalSquare
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuPullbackCompat
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NuPull

theorem nu_pull {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ}
    (hT : Mid.TeichmullerCongruence r N) {M M' : Model l K} (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p) (n j : ℕ)
    (x : B.Hc (B.schFn M'.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.pullHc (okToOC l K) (B.schMap u hu) true n j x) = pullM r u hu n j (Mid.nu r M' n j hT x) := by
  unfold Mid.nu pullM B.pullHc Mid.nuMor pullT' B.pullMorC
  exact (cr_square (Mid.mOut r M' n hT)
    (B.crMor (F := B.schFn M'.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism ((B.schMap u hu).ptK _) fun _ _ _ => rfl)
    (B.crMor (F := B.schFn M'.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism ((B.schMap u hu).ptK _) fun _ _ _ => rfl)
    (Mid.mOut r M n hT)
    (Mid.phiP_cris n N) (fun _ => rfl) (fun _ => rfl) (Mid.phiP_cris n N) (fun _ => rfl) (fun _ _ => rfl) j x).symm

end GlobalTheory.CompanionTheory.NuPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuReductionCompat
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NuRed

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem red_phiP {m n : ℕ} (h : n ≤ m) (N : ℕ) (x : (base l).Acr m) :
    (base l).red h (Mid.phiP l m N x) = Mid.phiP l n N ((base l).red h x) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Mid.phiP_succ, Mid.phiP_succ, ← ih]; exact (pdOk_frob _).red_acr h _

def redLm (r : CrystallineSemistableComparison.Res l K) (M : Model l K) {m n : ℕ} (h : n ≤ m) :
    Mor (Mid.Lm r M m) (Mid.Lm r M n) ((base l).red h) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true m) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    ((base l).red h) rfl (B.dd_red true _ h) (B.basePt _ _ (red_κm r h)) fun _ _ _ => rfl

def redLc (M : Model l K) {m n : ℕ} (h : n ≤ m) :
    Mor (B.Lc (B.schFn M.p) (okToOC l K) true m) (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).red h) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true m) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    ((base l).red h) rfl (B.dd_red true _ h) (B.basePt _ _ (B.red_κb _ true h)) fun _ _ _ => rfl

theorem ptOut_snd (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (F : B.Fn (OK l K)) (n : ℕ)
    (B₀ : CommRingCat.{0}) (y : (F.ptK (Mid.κm r n)).obj B₀) :
    ((Mid.ptOut F n hT).app B₀ y).1.2 = y.1.2 := rfl

theorem nu_pt (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (F : B.Fn (OK l K)) {m n : ℕ} (h : n ≤ m)
    (B₀ : CommRingCat.{0}) (y : (F.ptK (Mid.κm r n)).obj B₀) :
    ((Mid.ptOut F m hT).app B₀ ((B.basePt F _ (red_κm r h)).app B₀ y)).1.2 =
      ((B.basePt F _ (B.red_κb _ true h)).app B₀ ((Mid.ptOut F n hT).app B₀ y)).1.2 := by
  rw [ptOut_snd, SH.base_snd, SH.base_snd, ptOut_snd]

theorem nu_red : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ}
    (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true (n + 1) j),
    (redT r M (Nat.le_succ n)).pull j (Mid.nu r M (n + 1) j hT x) =
      Mid.nu r M n j hT (B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j x) := by
  intro l _ K r N hT M n j x
  unfold Mid.nu Mid.nuMor B.redHc B.redMor redT
  exact cr_square (Mid.mOut r M (n + 1) hT) (redLm r M (Nat.le_succ n)) (redLc M (Nat.le_succ n)) (Mid.mOut r M n hT)
    (Mid.phiP_cris _ N) (B.red_cris _ (Nat.le_succ n)) (B.red_cris _ (Nat.le_succ n)) (Mid.phiP_cris _ N)
    (red_phiP (Nat.le_succ n) N) (nu_pt r hT _ (Nat.le_succ n)) j x

end GlobalTheory.CompanionTheory.NuRed
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopGradedQuotientInjectiveMapStatement
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_graded_quotient_injective_map : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (r : ℤ), r = d → d + 1 ≤ s →
    letI := (strV q W).toAlgebra
    ∃ φ : HQ (KS q s {W}) r (r + 1) d →ₗ[K] Γ(X, W), Function.Injective φ ∧ ∀ (y : Γ(X, W)) (c : HQ (KS q s {W}) r (r + 1) d),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c → φ c = y := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.coef_map | exact GlobalTheory.CompanionTheory.ConeLocal.coef_map | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.coef_map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentPreservesFlag
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.FlagCent

variable {K : Type} [Field K] {n : ℕ}

theorem img_mul (g h : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img (g * h) W = img g (img h W) := by
  simp only [img, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

theorem img_one (W : Submodule K (Fin n → K)) : img (1 : GL (Fin n) K) W = W := by
  simp [img]

theorem mem_img_iff (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) (y : Fin n → K) :
    y ∈ img g W ↔ (g⁻¹ : GL (Fin n) K).val *ᵥ y ∈ W := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (g⁻¹ : GL (Fin n) K).val * g.val = 1 := by rw [← Units.val_mul]; simp
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, this] using hx
  · intro h
    refine ⟨_, h, ?_⟩
    simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec]

theorem form_mulVec (σ : K →+* K) (A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    ∑ i, σ ((A *ᵥ x) i) * y i = ∑ j, σ (x j) * ((A.map σ)ᵀ *ᵥ y) j := by
  simp only [mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, transpose_apply,
    map_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem perp_img (σ : K →+* K) (g : GL (Fin n) K) (X : Submodule K (Fin n → K)) :
    perp σ (img g X) = img (thetaR σ n g) (perp σ X) := by
  ext y
  rw [mem_img_iff]
  have hinv : ((thetaR σ n g)⁻¹ : GL (Fin n) K).val = (g.val.map σ)ᵀ := rfl
  rw [hinv]
  constructor
  · intro h x hx
    rw [← form_mulVec]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    rw [Matrix.toLin'_apply, form_mulVec]
    exact h x hx

theorem le_perp_perp (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (W : Submodule K (Fin n → K)) :
    W ≤ perp σ (perp σ W) := fun z hz y hy => by
  have h2 := congrArg σ (hy z hz)
  simp only [map_sum, map_mul, hσ, map_zero] at h2
  simpa [mul_comm] using h2

theorem perp_perp (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (W : Submodule K (Fin n → K)) :
    perp σ (perp σ W) = W := by
  refine le_antisymm (fun z hz => ?_) (le_perp_perp σ hσ W)
  by_contra hn
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_notMem hn
  let a : Fin n → K := fun i => f fun j => if i = j then 1 else 0
  have hfa : ∀ x, f x = ∑ i, x i * a i := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ f x]; rfl
  have hy : (fun i => σ (a i)) ∈ perp σ W := fun x hx => by
    have h0 : f x = 0 := hf hx
    rw [hfa] at h0
    have := congrArg σ h0
    simpa only [map_sum, map_mul, map_zero] using this
  have h1 := hz _ hy
  simp only [hσ] at h1
  exact hf0 (by rw [hfa]; simpa [mul_comm] using h1)

theorem perpD_perpD (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (d : GL (Fin n) K)
    (W : Submodule K (Fin n → K)) :
    perpD σ d (perpD σ d W) = img (d * thetaR σ n d) W := by
  simp only [perpD]
  rw [perp_img, perp_perp σ hσ, img_mul]

theorem thetaR_thetaR (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (g : GL (Fin n) K) :
    thetaR σ n (thetaR σ n g) = g := by
  apply Units.ext
  rw [thetaR_val]
  have hinv : ((thetaR σ n g)⁻¹ : GL (Fin n) K).val = (g.val.map σ)ᵀ := rfl
  rw [hinv]
  ext i j
  simp [hσ]

theorem commute_norm (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {d t : GL (Fin n) K}
    (ht : t ∈ twCent (thetaR σ n) d) :
    t * (d * thetaR σ n d) = (d * thetaR σ n d) * t := by
  have h1 : t⁻¹ * d * thetaR σ n t = d := ht
  have h2 : thetaR σ n d = (thetaR σ n t)⁻¹ * thetaR σ n d * t := by
    conv_lhs => rw [← h1]
    rw [map_mul, map_mul, map_inv, thetaR_thetaR σ hσ]
  have h3 : t * d = d * thetaR σ n t := by
    calc t * d = t * (t⁻¹ * d * thetaR σ n t) := by rw [h1]
      _ = d * thetaR σ n t := by group
  have h4 : thetaR σ n t * thetaR σ n d = thetaR σ n d * t := by
    calc thetaR σ n t * thetaR σ n d
        = thetaR σ n t * ((thetaR σ n t)⁻¹ * thetaR σ n d * t) := by rw [← h2]
      _ = thetaR σ n d * t := by group
  rw [← mul_assoc, h3, mul_assoc, h4, ← mul_assoc]

theorem map_le_of_commute [IsAlgClosed K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f t : Module.End K V) (hs : LinearMap.charpoly f |>.Separable)
    (hc : Commute f t) (W : Submodule K V) (hW : ∀ x ∈ W, f x ∈ W) : W.map t ≤ W := by
  have hW' : W = ⨆ μ, W ⊓ f.maxGenEigenspace μ := by
    have h := Submodule.inf_iSup_genEigenspace (p := W) (f := f) hW ⊤
    rw [show ⨆ μ, f.genEigenspace μ ⊤ = ⊤ from Module.End.iSup_maxGenEigenspace_eq_top f,
      inf_top_eq] at h
    exact h
  rw [Submodule.map_le_iff_le_comap]
  conv_lhs => rw [hW']
  refine iSup_le fun μ x hx => ?_
  have hdim : Module.finrank K (f.maxGenEigenspace μ) ≤ 1 := by
    rw [LinearMap.finrank_maxGenEigenspace_eq]
    exact Polynomial.rootMultiplicity_le_one_of_separable hs μ
  have htx : t x ∈ f.maxGenEigenspace μ := Module.End.mapsTo_maxGenEigenspace_of_comm hc μ hx.2
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 hdim
  obtain ⟨a, ha⟩ := hv ⟨x, hx.2⟩
  obtain ⟨b, hb⟩ := hv ⟨t x, htx⟩
  have ha' : a • (v : V) = x := congrArg Subtype.val ha
  have hb' : b • (v : V) = t x := congrArg Subtype.val hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx0 (by simpa using ha'.symm)
  change t x ∈ W
  rw [← hb', show b • (v : V) = (b / a) • x by rw [← ha', smul_smul, div_mul_cancel₀ _ ha0]]
  exact W.smul_mem _ hx.1

theorem img_eq_of_commute [IsAlgClosed K] (γ t : GL (Fin n) K) (hs : γ.val.charpoly.Separable)
    (hc : t * γ = γ * t) (W : Submodule K (Fin n → K)) (hW : img γ W = W) : img t W = W := by
  have key : ∀ s : GL (Fin n) K, s * γ = γ * s → img s W ≤ W := fun s hcs => by
    refine map_le_of_commute (Matrix.toLin' γ.val) (Matrix.toLin' s.val)
      (by rwa [Matrix.charpoly_toLin']) ?_ W fun x hx => ?_
    · change Matrix.toLin' γ.val * Matrix.toLin' s.val = Matrix.toLin' s.val * Matrix.toLin' γ.val
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
        ← Units.val_mul, ← Units.val_mul, hcs]
    · rw [← hW]; exact ⟨x, hx, rfl⟩
  refine le_antisymm (key t hc) ?_
  have hinv : t⁻¹ * γ = γ * t⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, hc]
  calc W = img t (img t⁻¹ W) := by rw [← img_mul, mul_inv_cancel, img_one]
    _ ≤ img t W := Submodule.map_mono (key t⁻¹ hinv)

theorem twCent_preserves_flag [IsAlgClosed K] (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x)
    (d : GL (Fin n) K) (hd : (d * thetaR σ n d).val.charpoly.Separable)
    (W₁ W₂ : Submodule K (Fin n → K)) (h₁ : perpD σ d W₁ = W₂) (h₂ : perpD σ d W₂ = W₁)
    {t : GL (Fin n) K} (ht : t ∈ twCent (thetaR σ n) d) : img t W₁ = W₁ ∧ img t W₂ = W₂ := by
  have hc := commute_norm σ hσ ht
  refine ⟨img_eq_of_commute _ t hd hc _ ?_, img_eq_of_commute _ t hd hc _ ?_⟩
  · rw [← perpD_perpD σ hσ, h₁, h₂]
  · rw [← perpD_perpD σ hσ, h₂, h₁]

end GlobalTheory.CompanionTheory.FlagCent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedGradedGenerationGlobalSections
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

lemma restrictTop_top_self {X : Scheme.{0}} (r : Γ(X, ⊤)) : restrictTop (⊤ : X.Opens) r = r := by
  change (X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op).hom r = r
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, X.presheaf.map_id]
  rfl

lemma twist_map_comp_app {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {F G K : X.Modules}
    (φ : F ⟶ G) (ψ : G ⟶ K) (V : X.Opens) (s : Γ(GlobalTheory.twist F L, V)) :
    (GlobalTheory.Twist.map L (φ ≫ ψ)).app V s = (GlobalTheory.Twist.map L ψ).app V ((GlobalTheory.Twist.map L φ).app V s) := by
  rw [GlobalTheory.Twist.map_comp]
  rfl

lemma smul_mem_twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (e : ℕ) {a : A} (ha : a ∈ I)
    {m : Γ(GlobalTheory.twistZ P H n, ⊤)} (hm : m ∈ twPow I H n P e) :
    toFunctions (X := X) (A := A) ⊤ a • m ∈ twPow I H n P (e + 1) := by
  have hm' : m ∈ (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ e) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) := hm
  change _ ∈ (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤))
  have hmem : toFunctions (X := X) (A := A) ⊤ a ∈ Ideal.map (toFunctions (X := X) (A := A) ⊤) I :=
    Ideal.mem_map_of_mem _ ha
  rw [pow_succ', Ideal.map_mul, mul_smul]
  exact Submodule.smul_mem_smul hmem hm'

theorem lifts_succ : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A), (∀ i, g i ∈ I) → ∀ (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (n : ℤ) (e : ℕ), Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) = ⊤ → Lifts I H hS n e → Lifts I H hS n (e + 1) := by
  intro A _ _ I X _ H P S hS k g hg hr n e hspan hL y
  have hy : y ∈ Submodule.span Γ(X, ⊤) (⋃ i, Set.range
      ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) := by
    rw [hspan]; trivial
  have hsub : ∀ m : ℕ, ∀ a b : Γ(GlobalTheory.twistZ P H n, ⊤), a ∈ twPow I H n P m → b ∈ twPow I H n P m →
      a + b ∈ twPow I H n P m := fun m a b ha hb =>
    Submodule.add_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) ha hb
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, y', rfl⟩ := Set.mem_iUnion.1 hy
    obtain ⟨c', rfl, hc'⟩ := hL y'
    refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (mulLvl (hr i) e)).app ⊤ c', ?_, ?_⟩
    · rw [← twist_map_comp_app, ← twist_map_comp_app, grπ_grT]
    · rw [← twist_map_comp_app, mulLvl_arrow, twist_map_comp_app, twist_smulHom_app,
        restrictTop_top_self]
      exact smul_mem_twPow I H n P e (hg i) hc'
  | zero =>
    refine ⟨0, map_zero _, ?_⟩
    rw [map_zero]
    exact Submodule.zero_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤))
  | add x y _ _ hx hy =>
    obtain ⟨c₁, rfl, h₁⟩ := hx
    obtain ⟨c₂, rfl, h₂⟩ := hy
    refine ⟨c₁ + c₂, map_add _ _ _, ?_⟩
    rw [map_add]
    exact hsub _ _ _ h₁ h₂
  | smul a x _ hx =>
    obtain ⟨c, rfl, h⟩ := hx
    refine ⟨a • c, Scheme.Modules.Hom.app_smul _ _ _, ?_⟩
    rw [Scheme.Modules.Hom.app_smul]
    exact Submodule.smul_mem (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ (e + 1)) •
      ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) a h

end GlobalTheory.CompanionTheory.GE.Step
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsCauchyLimitStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_sections_cauchy_limit : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ m, f m - f (m + 1) ∈ twPow I H n P m) → ∃ L : Γ(GlobalTheory.twistZ P H n, ⊤), ∀ m, f m - L ∈ twPow I H n P m := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_limit_twPow | exact GlobalTheory.CompanionTheory.GE.exists_limit_twPow | (intros; apply GlobalTheory.CompanionTheory.GE.exists_limit_twPow <;> assumption)
end

