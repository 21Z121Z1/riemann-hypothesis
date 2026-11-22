import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinPolarisationKernelLeUnitKernel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam

open Matrix

def formPolUnit (d : ℕ) : ord d :=
  ⟨form d * single (Sum.inl 0) (Sum.inr 0) 1, fun i j => by simp [Matrix.mul_apply, Matrix.single_apply]⟩

theorem idem_mul_formPolUnit (d : ℕ) : idem d * formPolUnit d = polUnit d := by
  ext1
  show single (Sum.inl 0) (Sum.inl 0) 1 * (form d * single (Sum.inl 0) (Sum.inr 0) 1) = single (Sum.inl 0) (Sum.inr 0) 1
  rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single]
  simp [form]

theorem bar_formPolUnit_mul_idem {d : ℕ} (hd : 0 < d) : bar d (formPolUnit d) * idem d = bar d (formPolUnit d) := by
  ext1
  have e : ((bar d (formPolUnit d) : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) =
      form d * single (Sum.inr 0) (Sum.inl 0) 1 := by
    rw [bar_coe]
    show form d * (form d * single (Sum.inl 0) (Sum.inr 0) 1)ᵀ * formInv d = _
    rw [Matrix.transpose_mul, form_transpose, Matrix.transpose_single, Matrix.mul_assoc, Matrix.mul_assoc,
      form_mul_formInv hd, Matrix.mul_one]
  rw [Subring.coe_mul, e]
  show form d * single (Sum.inr 0) (Sum.inl 0) 1 * single (Sum.inl 0) (Sum.inl 0) 1 = _
  rw [Matrix.mul_assoc, Matrix.single_mul_single_same, _root_.mul_one]

end GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinFam.KerSup

variable {X Y : Scheme.{0}}

theorem exists_gen_of_lbIso' {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (h : LBIso P Q)
    (H : ∃ t : LB.Gen P, t.IsGen) : ∃ t : LB.Gen Q, t.IsGen := by
  obtain ⟨w, hw⟩ := h.chartPull (chartPullId P) (chartPullPull Q (𝟙 X))
  obtain ⟨t, ht⟩ := H
  obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull P (𝟙 X)) t ht
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hQ hP a ha
  exact gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc

theorem gen_pull_comp (L : LB X) (f : Y ⟶ X) {Y' : Scheme.{0}} (h : Y' ⟶ Y)
    (H : ∃ t : LB.Gen (L.pull f), t.IsGen) : ∃ t : LB.Gen (L.pull (h ≫ f)), t.IsGen := by
  obtain ⟨t, ht⟩ := H
  exact gen_chartPull (chartPullSame L (fun _ => h ≫ f) (fun _ => f) (fun _ => 1) h (fun _ => rfl)) t ht

theorem gen_congr (L : LB X) {f g : Y ⟶ X} (e : f = g)
    (H : ∃ t : LB.Gen (L.pull f), t.IsGen) : ∃ t : LB.Gen (L.pull g), t.IsGen := by
  subst e; exact H

theorem lbIso_pull_comp (L : LB X) {f g : Y ⟶ X} {Y' : Scheme.{0}} (h : Y' ⟶ Y) (H : LBIso (L.pull f) (L.pull g)) :
    LBIso (L.pull (h ≫ f)) (L.pull (h ≫ g)) :=
  H.chartPull (chartPullSame L (fun _ => h ≫ f) (fun _ => f) (fun _ => 1) h (fun _ => rfl))
    (chartPullSame L (fun _ => h ≫ g) (fun _ => g) (fun _ => 1) h (fun _ => rfl))

theorem lbIso_pull_pull {L : LB X} {M : LB Y} {j : X ⟶ Y} {Y' : Scheme.{0}} (h : Y' ⟶ X) (H : LBIso L (M.pull j)) :
    LBIso (L.pull h) (M.pull (h ≫ j)) := by
  have a : ChartPull (L.pull h) L h := chartPullPull L h
  have b : ChartPull (M.pull (h ≫ j)) (M.pull j) h :=
    chartPullSame M (fun _ => h ≫ j) (fun _ => j) (fun _ => 1) h (fun _ => rfl)
  exact LBIso.chartPull a b H

end GlobalTheory.ZarhinFam.KerSup

namespace GlobalTheory.ZarhinFam

theorem ker_pol_le_ker_polUnit : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), (∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen) → x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 := by
  intro h M d hd S t c z act inc pr hdu hker hz hact hadj hinc hpr hip hpi hP T x hx
  have hNp : act (polUnit d) = act (idem d) ≫ act (formPolUnit d) := by
    rw [← idem_mul_formPolUnit, hact.2.2.1]
  have hbar : act (bar d (formPolUnit d)) ≫ pr ≫ inc = act (bar d (formPolUnit d)) := by
    rw [hpi, ← hact.2.2.1, bar_formPolUnit_mul_idem hd]
  have hy : x ≫ inc ≫ act (polUnit d) = x ≫ inc ≫ act (formPolUnit d) := by
    rw [hNp, ← hpi]
    simp only [Category.assoc]
    rw [← Category.assoc inc pr, hip, Category.id_comp]
  rw [hy]
  apply hz.2 T
  let q : z.A ⟶ c.A := act (bar d (formPolUnit d)) ≫ pr
  let ψ₁ : z.A ⊗ T ⟶ c.A ⊗ c.A := lift (snd z.A T ≫ x) (fst z.A T ≫ q)
  let φ : z.A ⊗ T ⟶ z.A ⊗ z.A := lift (snd z.A T ≫ x ≫ inc) (fst z.A T)
  have g1 : ∃ u : (c.P.pull ψ₁.left).Gen, u.IsGen := by
    have := KerSup.gen_pull_comp c.P _ (lift (fst z.A T ≫ q) (snd z.A T)).left hx
    refine KerSup.gen_congr c.P ?_ this
    rw [← Over.comp_left]
    congr 1
    simp [ψ₁]
  have g2 : ∃ u : (z.P.pull (ψ₁.left ≫ (inc ⊗ₘ inc).left)).Gen, u.IsGen :=
    KerSup.exists_gen_of_lbIso' (pull_isLB c.isLB _) (pull_isLB z.isLB _) (KerSup.lbIso_pull_pull ψ₁.left hP) g1
  have e3 : ψ₁.left ≫ (inc ⊗ₘ inc).left =
      φ.left ≫ (lift (fst z.A z.A) (snd z.A z.A ≫ act (bar d (formPolUnit d)))).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp only [ψ₁, φ, q, lift_map, comp_lift, lift_fst, lift_snd_assoc, Category.assoc, hbar]
  have i4 := KerSup.lbIso_pull_comp z.P φ.left (hadj (formPolUnit d))
  have g4 := KerSup.exists_gen_of_lbIso' (pull_isLB z.isLB _) (pull_isLB z.isLB _) i4.symm
    (KerSup.gen_congr z.P e3 g2)
  refine KerSup.gen_congr z.P ?_ g4
  rw [← Over.comp_left]
  congr 1
  simp [φ]

end GlobalTheory.ZarhinFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinPolarisationUnitKernelLeKernel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinKer

open Matrix GlobalTheory.ZarhinFam

def kerN (d : ℕ) : ord d :=
  ⟨form d * single (Sum.inl 0) (Sum.inr 0) 1, fun i j => by simp [Matrix.mul_apply, single]⟩

def kerM (d : ℕ) : ord d :=
  ⟨single (Sum.inl 0) (Sum.inr 0) 1 * formInv d, fun i j => by simp [Matrix.mul_apply, single]⟩

theorem idem_mul_kerN (d : ℕ) : idem d * kerN d = polUnit d := by
  ext1
  simp only [Subring.coe_mul, idem, kerN, polUnit_coe]
  rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single]
  simp [form]

theorem kerM_mul_bar_kerN {d : ℕ} (hd : 0 < d) : kerM d * bar d (kerN d) = idem d := by
  ext1
  simp only [Subring.coe_mul, bar_coe, kerM, kerN, idem, Matrix.transpose_mul, transpose_single, form_transpose]
  calc single (Sum.inl 0) (Sum.inr 0) (1 : ℤ) * formInv d *
        (form d * (single (Sum.inr 0) (Sum.inl 0) 1 * form d) * formInv d)
      = single (Sum.inl 0) (Sum.inr 0) (1 : ℤ) * (formInv d * form d) * single (Sum.inr 0) (Sum.inl 0) 1 *
          (form d * formInv d) := by simp only [Matrix.mul_assoc]
    _ = single (Sum.inl 0) (Sum.inl 0) 1 := by
      rw [formInv_mul_form hd, form_mul_formInv hd, Matrix.mul_one, Matrix.mul_one, single_mul_single_same, _root_.one_mul]

end GlobalTheory.ZarhinKer

namespace GlobalTheory.ZarhinKer

open GlobalTheory.ZarhinFam

theorem polUnit_ker_le : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 → ∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen := by
  intro h M d hd S t c z act inc pr _hdu _hker _hprin hact hadj _hinc _hpr hip hpi hP T x hx
  have hinc_idem : inc ≫ act (idem d) = inc := by
    rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have hN : inc ≫ act (kerN d) = inc ≫ act (polUnit d) := by
    calc inc ≫ act (kerN d) = (inc ≫ act (idem d)) ≫ act (kerN d) := by rw [hinc_idem]
      _ = inc ≫ act (polUnit d) := by rw [Category.assoc, ← hact.2.2.1, idem_mul_kerN]
  have hM : inc ≫ act (kerM d) ≫ act (bar d (kerN d)) = inc := by
    rw [← hact.2.2.1, kerM_mul_bar_kerN hd, hinc_idem]
  have hv : (snd c.A T ≫ x ≫ inc) ≫ act (kerN d) = 1 := by
    rw [Category.assoc, Category.assoc, hN, hx, comp_one]
  have e1 : ((fst c.A T ≫ inc ≫ act (kerM d)) ≫ lift (1 : z.A ⟶ z.A) (𝟙 z.A)).left =
      (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc ≫ act (kerM d))).left ≫
        (lift (fst z.A z.A ≫ act (kerN d)) (snd z.A z.A)).left := by
    rw [← Over.comp_left]
    congr 1
    ext1
    · simp only [Category.assoc, lift_fst, lift_fst_assoc, comp_one]
      rw [← hv]; simp only [Category.assoc]
    · simp only [Category.assoc, lift_snd, lift_snd_assoc, Category.comp_id]
  have e2 : (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc)).left =
      (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc ≫ act (kerM d))).left ≫
        (lift (fst z.A z.A) (snd z.A z.A ≫ act (bar d (kerN d)))).left := by
    rw [← Over.comp_left]
    congr 1
    ext1
    · simp only [Category.assoc, lift_fst, lift_fst_assoc]
    · simp only [Category.assoc, lift_snd, lift_snd_assoc, hM]
  have e3 : (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc)).left =
      (lift (snd c.A T ≫ x) (fst c.A T)).left ≫ (inc ⊗ₘ inc).left := by
    rw [← Over.comp_left]
    congr 1
    rw [lift_map, Category.assoc]
  have i1 := GlobalTheory.GenSpread.lbIso_pull_comp _ e1 e2 (hadj (kerN d))
  have i2 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP (lift (snd c.A T ≫ x) (fst c.A T)).left e3
  obtain ⟨t0, ht0⟩ := z.rig₁
  have g1 : ∃ u : LB.Gen (z.P.pull ((fst c.A T ≫ inc ≫ act (kerM d)) ≫ lift (1 : z.A ⟶ z.A) (𝟙 z.A)).left),
      u.IsGen :=
    ⟨LB.pullGen z.P _ _ t0 (fst c.A T ≫ inc ≫ act (kerM d)).left,
      LB.isGen_pullGen z.P _ _ t0 ht0 (fst c.A T ≫ inc ≫ act (kerM d)).left⟩
  have g2 := GlobalTheory.RigidBundleGlue.exists_gen_of_lbIso (pull_isLB z.isLB _) (pull_isLB z.isLB _) i1 g1
  exact GlobalTheory.RigidBundleGlue.exists_gen_of_lbIso (pull_isLB z.isLB _) (pull_isLB c.isLB _) i2.symm g2

end GlobalTheory.ZarhinKer
end
end

