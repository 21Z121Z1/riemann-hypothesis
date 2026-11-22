import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfB
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CountableOfIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecOfLocal
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.FieldBaseChange

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {Y Y' X₁ X₂ Z₁ Z₂ Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}

def isoVal (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (r : Z ⟶ Y) (z : Z) (i₂ : L₂.ι) (i₁ : L₁.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z ((L₂.pull f₂).U (fun _ => i₂) ⊓ (L₁.pull f₁).U (fun _ => i₁)) (w.s (fun _ => i₂, fun _ => i₁))

theorem isoVal_trans {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen) (r : Z ⟶ Y) (z : Z)
    {i₂ j₂ : L₂.ι} {i₁ j₁ : L₁.ι} (a₂ : f₂ (r z) ∈ L₂.U i₂) (b₂ : f₂ (r z) ∈ L₂.U j₂)
    (a₁ : f₁ (r z) ∈ L₁.U i₁) (b₁ : f₁ (r z) ∈ L₁.U j₁) :
    isoVal w r z i₂ i₁ = gm (r ≫ f₂) z _ (L₂.g i₂ j₂) * (gm (r ≫ f₁) z _ (L₁.g i₁ j₁))⁻¹ * isoVal w r z j₂ j₁ := by
  have := (isGen_iff w).1 hw _ r z i₂ j₂ (fun _ => i₁) (fun _ => j₁) a₂ b₂ (mem_pull.2 a₁) (mem_pull.2 b₁)
  exact this.trans (congrArg (fun u => _ * u⁻¹ * _)
    (gm_pull_g L₁ f₁ r z (fun _ => i₁) (fun _ => j₁) (mem_pull.2 a₁) (mem_pull.2 b₁)))

def powVal {L : LB X₁} {g : Z₁ ⟶ X₁} {k : ℤ} (a : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k)))
    (r : Z ⟶ Z₁) (z : Z) (i : L.ι) : Z.presheaf.stalk z :=
  gs r z (LB.wchart L (fun _ : Fin 1 => g) (fun _ => i)) (a.f (fun _ => i))

theorem sval_eq_powVal {L : LB X₁} {g : Z₁ ⟶ X₁} {k : ℤ}
    (a : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))) (r : Z ⟶ Z₁) (z : Z)
    (J : (Z ⟶ X₁) → L.ι) : sval a r z J = powVal a r z (J (r ≫ g)) := rfl

theorem powVal_trans {L : LB X₁} {g : Z₁ ⟶ X₁} {k : ℤ}
    (a : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))) (r : Z ⟶ Z₁) (z : Z) {i j : L.ι}
    (hi : g (r z) ∈ L.U i) (hj : g (r z) ∈ L.U j) :
    powVal a r z i = (gm (r ≫ g) z _ (L.g i j) ^ k).val * powVal a r z j :=
  (sec_trans a r z (mem_wchart.2 fun _ => hi) (mem_wchart.2 fun _ => hj)).trans
    (congrArg (fun u : (Z.presheaf.stalk z)ˣ => u.val * _) (Fin.prod_univ_one _))

theorem exists_sec_of_local {L : LB X₂} {g : Y' ⟶ X₂} {k : ℤ} {I : Type} (W : I → Y'.Opens)
    (hW : ∀ y, ∃ p, y ∈ W p)
    (u : ∀ (i : L.ι) (p : I), Γ(Y', LB.wchart L (fun _ : Fin 1 => g) (fun _ => i) ⊓ W p))
    (v : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y') (z : Z), L.ι → I → Z.presheaf.stalk z)
    (huv : ∀ Z r z i p, g (r z) ∈ L.U i → r z ∈ W p → gs r z _ (u i p) = v Z r z i p)
    (h₁ : ∀ y i p p', g y ∈ L.U i → y ∈ W p → y ∈ W p' → v _ (𝟙 Y') y i p = v _ (𝟙 Y') y i p')
    (h₂ : ∀ y i i' p, g y ∈ L.U i → g y ∈ L.U i' → y ∈ W p →
      v _ (𝟙 Y') y i p = (gm (𝟙 Y' ≫ g) y _ (L.g i i') ^ k).val * v _ (𝟙 Y') y i' p) :
    ∃ b : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k)),
      ∀ Z r z i p, g (r z) ∈ L.U i → r z ∈ W p → powVal b r z i = v Z r z i p := by
  have glue : ∀ i : L.ι, ∃ a : Γ(Y', LB.wchart L (fun _ : Fin 1 => g) (fun _ => i)),
      ∀ Z r z p, g (r z) ∈ L.U i → r z ∈ W p → gs r z _ a = v Z r z i p := fun i => by
    obtain ⟨a, ha, -⟩ := sec_glue (LB.wchart L (fun _ : Fin 1 => g) (fun _ => i))
      (fun p => LB.wchart L (fun _ : Fin 1 => g) (fun _ => i) ⊓ W p) (fun _ => inf_le_left)
      (fun y hy => by
        obtain ⟨p, hp⟩ := hW y
        exact Opens.mem_iSup.2 ⟨p, hy, hp⟩) (u i) (fun p p' => fn_ext fun y hy => by
        have hi := mem_wchart.1 hy.1.1 0
        exact ((gs_res (𝟙 Y') y inf_le_left hy _).trans (huv _ _ y i p hi hy.1.2)).trans
          ((h₁ y i p p' hi hy.1.2 hy.2.2).trans
            ((gs_res (𝟙 Y') y inf_le_right hy _).trans (huv _ _ y i p' hi hy.2.2)).symm))
    refine ⟨a, fun Z r z p hi hp => ?_⟩
    have hz : r z ∈ LB.wchart L (fun _ : Fin 1 => g) (fun _ => i) ⊓ W p := ⟨mem_wchart.2 fun _ => hi, hp⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z _) (ha p)).trans (huv Z r z i p hi hp))
  have glue' : ∀ j : Fin 1 → L.ι, ∃ a : Γ(Y', LB.wchart L (fun _ : Fin 1 => g) j),
      ∀ Z r z p, g (r z) ∈ L.U (j 0) → r z ∈ W p → gs r z _ a = v Z r z (j 0) p := fun j => by
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun t => congrArg j (Subsingleton.elim _ _)⟩
    exact glue i
  choose a ha using glue'
  refine ⟨⟨a, fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => ?_⟩, fun Z r z i p hi hp => ha _ Z r z p hi hp⟩
  obtain ⟨p, hp⟩ := hW y
  have m := mem_wchart.1 hy.1 0
  have m' := mem_wchart.1 hy.2 0
  refine ((gs_res (𝟙 Y') y _ hy _).trans (ha j _ _ y p m hp)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans (congrArg Units.val
      ((gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2).trans (Fin.prod_univ_one _))))
      ((gs_res (𝟙 Y') y _ hy _).trans (ha j' _ _ y p m' hp)))).symm)
  exact h₂ y _ _ p m m' hp

theorem gs_isoUnit (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (m : Y' ⟶ Y) (n : ℤ) (i₂ : L₂.ι) (i₁ : L₁.ι)
    {O : Y'.Opens} (hO : O ≤ m ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => i₂) ⊓ (L₁.pull f₁).U (fun _ => i₁)))
    (r : Z ⟶ Y') (z : Z) (hz : r z ∈ O) :
    gs r z O (res hO (pullU m _ (w.s (fun _ => i₂, fun _ => i₁))) ^ n).val = (isoVal w (r ≫ m) z i₂ i₁ ^ n).val :=
  (gs_unit r z O hz _).trans (congrArg Units.val ((map_zpow _ _ _).trans (congrArg (· ^ n)
    ((gm_res r z hO hz _).trans (gm_pull r m z _ (hO hz) _)))))

theorem exists_move (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen)
    (m : Y' ⟶ Y) (k : ℤ) {g₁ : Z₁ ⟶ X₁} (h₁ : Y' ⟶ Z₁) (e₁ : h₁ ≫ g₁ = m ≫ f₁) {g₂ : Y' ⟶ X₂} (e₂ : g₂ = m ≫ f₂)
    (a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => k))) :
    ∃ b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i₂ i₁, f₂ (m (r z)) ∈ L₂.U i₂ → f₁ (m (r z)) ∈ L₁.U i₁ →
        powVal b r z i₂ = (isoVal w (r ≫ m) z i₂ i₁ ^ k).val * powVal a (r ≫ h₁) z i₁ := by
  subst e₂
  have pt : ∀ y, g₁ (h₁ y) = f₁ (m y) := fun y => congrArg (fun q : Y' ⟶ X₁ => q y) e₁
  have l₁ : ∀ i₂ i₁, LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) (fun _ => i₂) ⊓ (m ≫ f₁) ⁻¹ᵁ L₁.U i₁ ≤
      m ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => i₂) ⊓ (L₁.pull f₁).U (fun _ => i₁)) := fun i₂ i₁ y hy =>
    ⟨mem_pull.2 (mem_wchart.1 hy.1 0), mem_pull.2 hy.2⟩
  have l₂ : ∀ i₂ i₁, LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) (fun _ => i₂) ⊓ (m ≫ f₁) ⁻¹ᵁ L₁.U i₁ ≤
      h₁ ⁻¹ᵁ LB.wchart L₁ (fun _ : Fin 1 => g₁) (fun _ => i₁) := fun i₂ i₁ y hy =>
    (mem_wchart (y := h₁ y)).2 fun _ => (pt y).symm ▸ hy.2
  refine exists_sec_of_local (fun i₁ => (m ≫ f₁) ⁻¹ᵁ L₁.U i₁) (fun y => exists_chart hL₁ _)
    (fun i₂ i₁ => (res (l₁ i₂ i₁) (pullU m _ (w.s (fun _ => i₂, fun _ => i₁))) ^ k).val *
      (Y'.presheaf.map (homOfLE (l₂ i₂ i₁)).op).hom ((h₁.app _).hom (a.f (fun _ => i₁))))
    (fun Z r z i₂ i₁ => (isoVal w (r ≫ m) z i₂ i₁ ^ k).val * powVal a (r ≫ h₁) z i₁)
    (fun Z r z i₂ i₁ a₂ a₁ => ?_) (fun y i₂ i₁ j₁ a₂ a₁ b₁ => ?_) (fun y i₂ j₂ i₁ a₂ b₂ a₁ => ?_)
  · have hz : r z ∈ LB.wchart L₂ (fun _ : Fin 1 => m ≫ f₂) (fun _ => i₂) ⊓ (m ≫ f₁) ⁻¹ᵁ L₁.U i₁ :=
      ⟨mem_wchart.2 fun _ => a₂, a₁⟩
    exact (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_isoUnit w m k i₂ i₁ _ r z hz)
      ((gs_res r z _ hz _).trans (gs_pull r h₁ z _ (l₂ i₂ i₁ hz) _)))
  · have c₁ : g₁ ((𝟙 Y' ≫ h₁) y) ∈ L₁.U i₁ := (pt y).symm ▸ a₁
    have c₂ : g₁ ((𝟙 Y' ≫ h₁) y) ∈ L₁.U j₁ := (pt y).symm ▸ b₁
    beta_reduce
    rw [isoVal_trans hw (𝟙 Y' ≫ m) y a₂ a₂ a₁ b₁, powVal_trans a (𝟙 Y' ≫ h₁) y c₁ c₂,
      gm_self hL₂ ((𝟙 Y' ≫ m) ≫ f₂) y a₂, Category.assoc, Category.assoc, e₁, ← mul_assoc, ← Units.val_mul]
    congr 2
    rw [one_mul, mul_zpow, inv_zpow, mul_comm, mul_inv_cancel_left]
  · beta_reduce
    rw [isoVal_trans hw (𝟙 Y' ≫ m) y a₂ b₂ a₁ a₁, gm_self hL₁ ((𝟙 Y' ≫ m) ≫ f₁) y a₁, inv_one, mul_one,
      mul_zpow, Units.val_mul, mul_assoc, Category.assoc]

theorem exists_move_back (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen)
    (m : Y' ⟶ Y) (k : ℤ) {g₂ : Z₂ ⟶ X₂} (h₂ : Y' ⟶ Z₂) (e₂ : h₂ ≫ g₂ = m ≫ f₂) {g₁ : Y' ⟶ X₁} (e₁ : g₁ = m ≫ f₁)
    (b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => k))) :
    ∃ a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i₂ i₁, f₂ (m (r z)) ∈ L₂.U i₂ → f₁ (m (r z)) ∈ L₁.U i₁ →
        powVal b (r ≫ h₂) z i₂ = (isoVal w (r ≫ m) z i₂ i₁ ^ k).val * powVal a r z i₁ := by
  subst e₁
  have pt : ∀ y, g₂ (h₂ y) = f₂ (m y) := fun y => congrArg (fun q : Y' ⟶ X₂ => q y) e₂
  have l₁ : ∀ i₁ i₂, LB.wchart L₁ (fun _ : Fin 1 => m ≫ f₁) (fun _ => i₁) ⊓ (m ≫ f₂) ⁻¹ᵁ L₂.U i₂ ≤
      m ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => i₂) ⊓ (L₁.pull f₁).U (fun _ => i₁)) := fun i₁ i₂ y hy =>
    ⟨mem_pull.2 hy.2, mem_pull.2 (mem_wchart.1 hy.1 0)⟩
  have l₂ : ∀ i₁ i₂, LB.wchart L₁ (fun _ : Fin 1 => m ≫ f₁) (fun _ => i₁) ⊓ (m ≫ f₂) ⁻¹ᵁ L₂.U i₂ ≤
      h₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => g₂) (fun _ => i₂) := fun i₁ i₂ y hy =>
    (mem_wchart (y := h₂ y)).2 fun _ => (pt y).symm ▸ hy.2
  obtain ⟨a, ha⟩ := exists_sec_of_local (L := L₁) (g := m ≫ f₁) (k := k) (fun i₂ => (m ≫ f₂) ⁻¹ᵁ L₂.U i₂)
    (fun y => exists_chart hL₂ _)
    (fun i₁ i₂ => (res (l₁ i₁ i₂) (pullU m _ (w.s (fun _ => i₂, fun _ => i₁))) ^ (-k)).val *
      (Y'.presheaf.map (homOfLE (l₂ i₁ i₂)).op).hom ((h₂.app _).hom (b.f (fun _ => i₂))))
    (fun Z r z i₁ i₂ => (isoVal w (r ≫ m) z i₂ i₁ ^ (-k)).val * powVal b (r ≫ h₂) z i₂)
    (fun Z r z i₁ i₂ a₁ a₂ => by
      have hz : r z ∈ LB.wchart L₁ (fun _ : Fin 1 => m ≫ f₁) (fun _ => i₁) ⊓ (m ≫ f₂) ⁻¹ᵁ L₂.U i₂ :=
        ⟨mem_wchart.2 fun _ => a₁, a₂⟩
      exact (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_isoUnit w m (-k) i₂ i₁ _ r z hz)
        ((gs_res r z _ hz _).trans (gs_pull r h₂ z _ (l₂ i₁ i₂ hz) _))))
    (fun y i₁ i₂ j₂ a₁ a₂ b₂ => by
      have c₁ : g₂ ((𝟙 Y' ≫ h₂) y) ∈ L₂.U i₂ := (pt y).symm ▸ a₂
      have c₂ : g₂ ((𝟙 Y' ≫ h₂) y) ∈ L₂.U j₂ := (pt y).symm ▸ b₂
      beta_reduce
      rw [isoVal_trans hw (𝟙 Y' ≫ m) y a₂ b₂ a₁ a₁, powVal_trans b (𝟙 Y' ≫ h₂) y c₁ c₂,
        gm_self hL₁ ((𝟙 Y' ≫ m) ≫ f₁) y a₁, Category.assoc, Category.assoc, e₂, ← mul_assoc, ← Units.val_mul]
      congr 2
      rw [inv_one, mul_one, mul_zpow, zpow_neg, mul_comm, mul_inv_cancel_left])
    (fun y i₁ j₁ i₂ a₁ b₁ a₂ => by
      beta_reduce
      rw [isoVal_trans hw (𝟙 Y' ≫ m) y a₂ a₂ a₁ b₁, gm_self hL₂ ((𝟙 Y' ≫ m) ≫ f₂) y a₂, one_mul,
        mul_zpow, inv_zpow', neg_neg, Units.val_mul, mul_assoc, Category.assoc])
  refine ⟨a, fun Z r z i₂ i₁ a₂ a₁ => ?_⟩
  rw [ha Z r z i₁ i₂ a₁ a₂, ← mul_assoc, ← Units.val_mul, zpow_neg, mul_inv_cancel, Units.val_one, one_mul]

theorem isoRelM_iff (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (m : Y' ⟶ Y) (k : ℕ) {g₁ : Z₁ ⟶ X₁} (h₁ : Y' ⟶ Z₁)
    (e₁ : h₁ ≫ g₁ = m ≫ f₁) {g₂ : Z₂ ⟶ X₂} (h₂ : Y' ⟶ Z₂) (e₂ : h₂ ≫ g₂ = m ≫ f₂)
    (a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ))))
    (b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ)))) :
    (GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a g₂ h₂ b →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i₂ i₁, f₂ (m (r z)) ∈ L₂.U i₂ → f₁ (m (r z)) ∈ L₁.U i₁ →
        powVal b (r ≫ h₂) z i₂ = (isoVal w (r ≫ m) z i₂ i₁ ^ (k : ℤ)).val * powVal a (r ≫ h₁) z i₁) ∧
    ((∀ (y : Y') i₂ i₁, f₂ (m y) ∈ L₂.U i₂ → f₁ (m y) ∈ L₁.U i₁ →
        powVal b (𝟙 Y' ≫ h₂) y i₂ = (isoVal w (𝟙 Y' ≫ m) y i₂ i₁ ^ (k : ℤ)).val * powVal a (𝟙 Y' ≫ h₁) y i₁) →
      GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a g₂ h₂ b) := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i₂ i₁ (O : Y'.Opens) (_ : r z ∈ O)
      (a₀ : O ≤ m ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => i₂) ⊓ (L₁.pull f₁).U (fun _ => i₁)))
      (a₁ : O ≤ h₁ ⁻¹ᵁ LB.wchart L₁ (fun _ : Fin 1 => g₁) (fun _ => i₁))
      (a₂ : O ≤ h₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => g₂) (fun _ => i₂)),
      gs r z O ((Y'.presheaf.map (homOfLE a₂).op).hom ((h₂.app _).hom (b.f (fun _ => i₂)))) =
        powVal b (r ≫ h₂) z i₂ ∧
      gs r z O ((res a₀ (pullU m _ (w.s (fun _ => i₂, fun _ => i₁)))).val ^ k *
        (Y'.presheaf.map (homOfLE a₁).op).hom ((h₁.app _).hom (a.f (fun _ => i₁)))) =
        (isoVal w (r ≫ m) z i₂ i₁ ^ (k : ℤ)).val * powVal a (r ≫ h₁) z i₁ := fun Z r z i₂ i₁ O hz a₀ a₁ a₂ =>
    ⟨(gs_res r z a₂ hz _).trans (gs_pull r h₂ z _ (a₂ hz) _), (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
      ((congrArg (gs r z O) (by rw [zpow_natCast, Units.val_pow_eq_pow_val])).trans
        (gs_isoUnit w m k i₂ i₁ a₀ r z hz)) ((gs_res r z a₁ hz _).trans (gs_pull r h₁ z _ (a₁ hz) _)))⟩
  have pt₁ : ∀ y, g₁ (h₁ y) = f₁ (m y) := fun y => congrArg (fun q : Y' ⟶ X₁ => q y) e₁
  have pt₂ : ∀ y, g₂ (h₂ y) = f₂ (m y) := fun y => congrArg (fun q : Y' ⟶ X₂ => q y) e₂
  constructor
  · intro H Z r z i₂ i₁ a₂ a₁
    have hz : r z ∈ GeneratorPullback.isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ (fun _ => i₂, fun _ => i₁) (fun _ => i₁) (fun _ => i₂) :=
      ⟨⟨⟨mem_pull.2 a₂, mem_pull.2 a₁⟩, (mem_wchart (y := h₁ (r z))).2 fun _ => (pt₁ _).symm ▸ a₁⟩,
        (mem_wchart (y := h₂ (r z))).2 fun _ => (pt₂ _).symm ▸ a₂⟩
    obtain ⟨k₁, k₂⟩ := key Z r z i₂ i₁ _ hz (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
      inf_le_right
    exact k₁.symm.trans ((congrArg (gs r z _) (H.2.2 (fun _ => i₂, fun _ => i₁) (fun _ => i₁) (fun _ => i₂)
      rfl rfl)).trans k₂)
  · intro H
    refine ⟨e₁, e₂, ?_⟩
    rintro ⟨p₁, p₂⟩ j₁ j₂ c₁ c₂
    obtain rfl : j₁ = fun _ => p₂ PUnit.unit := funext fun i => (congrArg j₁ (Subsingleton.elim i 0)).trans c₁
    obtain rfl : j₂ = fun _ => p₁ PUnit.unit := funext fun i => (congrArg j₂ (Subsingleton.elim i 0)).trans c₂
    refine fn_ext fun y hy => ?_
    obtain ⟨k₁, k₂⟩ := key _ (𝟙 Y') y (p₁ PUnit.unit) (p₂ PUnit.unit) _ hy (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right) inf_le_right
    exact k₁.trans ((H y _ _ (mem_pull.1 hy.1.1.1) (mem_pull.1 hy.1.1.2)).trans k₂.symm)

end GlobalTheory.FieldBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspKilledCoefficientEqZeroStatement
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxCusp_killedCoefficient_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), (∀ cu : CuspFD X ρ, ∃ bs, IsZBasis X cu bs) → ∀ (la : Wt X.Ψ r), (∀ (cu : CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), β ∈ zGam X cu → ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1) → ∀ (c : ℝ) (P : Frame X.Ψ r → ℂ), P ∈ X.SSgt la c → ∀ (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsExpoFD X cu χ → KilledFD X cu χ c → ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0 := by
  first | exact @GlobalTheory.MaxCuspKilled.coefFn_eq_zero_of_killed | exact GlobalTheory.MaxCuspKilled.coefFn_eq_zero_of_killed | (intros; apply GlobalTheory.MaxCuspKilled.coefFn_eq_zero_of_killed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspMemCuspFormsOfKilledCoefZero
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

namespace GlobalTheory

namespace MaxCuspBwd

open MeasureTheory Complex GlobalTheory.TorusFourier

theorem integral_eq_zero_of_coeffs {ι : Type} [Fintype ι] {N : ℕ} {Γ : AddSubgroup (ι → ℝ)}
    {D : Set (ι → ℝ)} (hD : IsAddFundamentalDomain Γ D volume) (h0 : volume D ≠ 0)
    (h1 : volume D ≠ ⊤) (L : (ι → ℝ) →ₗ[ℝ] (Fin N → ℝ)) (g : (Fin N → ℝ) → ℂ) (hc : Continuous g)
    (hper : ∀ u (n : Fin N → ℤ), g (u + fun i => (n i : ℝ)) = g u)
    (hL : ∀ p ∈ Γ, ∀ k, ∃ z : ℤ, L p k = z) (ν : ι → ℝ)
    (hν : ∀ p ∈ Γ, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k)
    (h : ∀ m : Fin N → ℤ, (∀ s, ∑ k, (m k : ℝ) * L s k = 2 * ∑ τ, ν τ * s τ) →
      ∫ t in cube N, g t * chr (fun k => (m k : ℝ)) t = 0) :
    ((volume D).toReal : ℂ)⁻¹ *
      ∫ s in D, g (L s) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) = 0 := by
  classical
  set ν' : (ι → ℝ) →ₗ[ℝ] ℝ := ∑ τ, (2 * ν τ) • LinearMap.proj τ with hν'd
  have hν'a : ∀ s, ν' s = 2 * ∑ τ, ν τ * s τ := fun s => by
    simp [hν'd, Finset.mul_sum, mul_assoc]
  have hf : ∀ i x, g (x + Pi.basisFun ℝ (Fin N) i) = g x := fun i x => by
    rw [← hper x (Pi.single i 1)]
    congr 2
    funext k
    by_cases hk : k = i <;> simp [hk]
  have hf₁ : ∀ l ∈ Γ, ∀ x, g (x + L l) = g x := fun l hl x => by
    choose z hz using hL l hl
    rw [← hper x z]
    congr 2
    funext k
    exact hz k
  have key := ((partialCoeff_spec_cube (Pi.basisFun ℝ (Fin N)) hD h0 h1 L hc hf hf₁).1 ν'
    (fun l hl => by rw [hν'a]; exact hν l hl)).2.2.2.2 (fun χ hχ hχL => by
      choose m hm using hχ
      have hsum : ∀ t : Fin N → ℝ, ∑ i, t i • Pi.basisFun ℝ (Fin N) i = t := fun t => by
        simpa using (Pi.basisFun ℝ (Fin N)).sum_repr t
      have hχa : ∀ t : Fin N → ℝ, χ t = ∑ k, t k * (m k : ℝ) := fun t => by
        conv_lhs => rw [← hsum t]
        simp only [map_sum, map_smul, hm, smul_eq_mul]
      have h2 := h m fun s => by
        rw [← hν'a, ← hχL, LinearMap.comp_apply, hχa]
        simp only [mul_comm]
      rw [← h2, cubeCoeff, cube, Set.pi_univ_Icc]
      simp only [hsum, eNeg, chr, hχa]
      rfl)
  have h3 := congrFun key 0
  rw [partialCoeff, coeff_eq] at h3
  simp only [zero_add, hν'a, Pi.zero_apply] at h3
  rw [← h3, Measure.real]
  congr 2
  funext s
  congr 2
  push_cast
  ring

end MaxCuspBwd

open MeasureTheory Complex in

theorem maxCusps_mem_SSgt_of_coef_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), (∀ ξ, X.IsIso ξ → ∃ cu : CuspFD X ρ, ξ ∈ Submodule.span E (Set.range cu.e)) → (∀ cu : CuspFD X ρ, ∃ bs, IsZBasis X cu bs) → ∀ (la : Wt X.Ψ r), (∀ (cu : CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), β ∈ zGam X cu → ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1) → ∀ (c : ℝ) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la → (∀ (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsExpoFD X cu χ → KilledFD X cu χ c → ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0) → P ∈ X.SSgt la c := by
  intro E _ _ _ r ρ X hcu hbas la hchi c P hP hK
  refine ⟨hP, fun ξ hξ ν hν x hx => ?_⟩
  obtain ⟨cu, hspan⟩ := hcu ξ hξ
  obtain ⟨η, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hspan
  have hb : IsZBasis X cu (zBas X cu) := Classical.epsilon_spec (hbas cu)
  obtain ⟨L, hflow, hph, hLint⟩ := GlobalTheory.T.cuspFlow_eq_torusAction E r ρ X cu hb η hξ.1
  have hη : η ≠ 0 := by
    rintro rfl
    exact hξ.2.2 (by simp)
  have hsec : X.IsSec la P := hP.1.1
  unfold Data.fj
  split_ifs with hfreq hdom
  · obtain ⟨-, hD, h0, h1⟩ := hdom.choose_spec
    simp only [hflow]
    refine MaxCuspBwd.integral_eq_zero_of_coeffs hD h0.ne' h1.ne L (fun u => P (zAct X cu u x))
      ?_ (maxCuspsA_periodic X cu hb la (hchi cu) P hsec x hx) (hLint la) ν hfreq fun m hm => ?_
    · exact hsec.1.continuousOn.comp_continuous (continuous_zAct X cu x)
        fun t => zAct_mem_dom X cu (zBas_skew X cu (hbas cu)) t x hx
    · obtain ⟨χ, hχ, hχm⟩ := GlobalTheory.T.hermitian_matrix_realizes_cusp_coords E r ρ X cu hb m
      have hνχ : ∀ τ : X.Ψ, (τ.1 (hq χ η)).re = ν τ := fun τ => by
        classical
        have h2 := hph χ hχ (Pi.single τ 1)
        simp only [hχm] at h2
        rw [hm] at h2
        simpa [Pi.single_apply] using h2.symm
      have h3 := hK cu χ ⟨hχ, fun k => ⟨m k, hχm k⟩⟩
        ⟨η, hη, hξ.1, by simpa only [hνχ] using hν⟩ x hx
      rw [show phZ X cu χ = fun k => (m k : ℝ) from funext hχm] at h3
      exact h3
  · rfl
  · rfl

end GlobalTheory
end

