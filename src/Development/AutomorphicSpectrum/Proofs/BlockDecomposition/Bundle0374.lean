import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliConstantTermVanishing
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix Topology

namespace GlobalTheory.CompanionTheory.CTFin.CapStable

theorem qdet_mem {a : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (X : Fin a → Fin a → A)
    (h : ∀ i j, X i j ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (h _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

def blockM {R : Type} [CommRing R] {r s : ℕ} (A : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin s) (Fin s) R) :
    Matrix (Fin (r + s)) (Fin (r + s)) R :=
  Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
    (fromBlocks A 0 0 B)

theorem val_lev {R : Type} [CommRing R] {r s : ℕ} (g : GL (Fin r) R × GL (Fin s) R) :
    (lev R r s g).val = blockM g.1.val g.2.val :=
  GlobalTheory.SmGL.val_emb₂ R _ g

theorem blockM_map {R S : Type} [CommRing R] [CommRing S] {r s : ℕ} (p : R →+* S)
    (A : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin s) (Fin s) R) :
    (blockM A B).map p = blockM (A.map p) (B.map p) := by
  ext i j
  simp only [blockM, Matrix.map_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

theorem map_lev {R S : Type} [CommRing R] [CommRing S] {r s : ℕ} (p : R →+* S)
    (g : GL (Fin r) R × GL (Fin s) R) :
    Matrix.GeneralLinearGroup.map p (lev R r s g) =
      lev S r s (Matrix.GeneralLinearGroup.map p g.1, Matrix.GeneralLinearGroup.map p g.2) := by
  apply Units.ext
  change (lev R r s g).val.map p = (lev S r s _).val
  rw [val_lev, val_lev, blockM_map]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem infGL_lev (y : GL (Fin r) (Cinf E) × GL (Fin s) (Cinf E)) :
    infGL E (r + s) (lev (Cinf E) r s y) = lev (Ad E) r s (infGL E r y.1, infGL E s y.2) := by
  refine ga_ext ?_ ?_
  · rw [map_lev]; simp
  · rw [map_lev]; simp only [pFin_infGL, pFin_infGL]; exact (map_one _).symm

theorem blockM_add {R : Type} [CommRing R] {r s : ℕ} (A A' : Matrix (Fin r) (Fin r) R)
    (B B' : Matrix (Fin s) (Fin s) R) : blockM A B + blockM A' B' = blockM (A + A') (B + B') := by
  ext i j
  simp only [blockM, Matrix.add_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

theorem blockM_smul {R : Type} [CommRing R] {r s : ℕ} (t : ℝ) [Module ℝ R] (A : Matrix (Fin r) (Fin r) R)
    (B : Matrix (Fin s) (Fin s) R) : t • blockM A B = blockM (t • A) (t • B) := by
  ext i j
  simp only [blockM, Matrix.smul_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

theorem one_add_smul_blockM (t : ℝ) (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) :
    1 + t • blockM X₁ X₂ = blockM (1 + t • X₁) (1 + t • X₂) := by
  have h1 : (1 : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) = blockM 1 1 := by
    simp [blockM, fromBlocks_one]
  rw [h1, blockM_smul, blockM_add]

theorem lieD_block {F : Sm E (r + s)} (hF : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0)
    (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) (m : GA E r × GA E s) :
    lieD (toL (blockM X₁ X₂)) F.1 (lev (Ad E) r s m) = 0 := by
  set g := lev (Ad E) r s m with hg
  set X : Lie E (r + s) := toL (blockM X₁ X₂) with hX
  let c : ℝ → Lie E (r + s) := fun t => oneL E (r + s) + t • X
  have hc : HasDerivAt c X 0 :=
    (((hasDerivAt_id' (0 : ℝ)).smul_const X).const_add (oneL E (r + s))).congr_deriv (one_smul ℝ X)
  have h0 : c 0 = oneL E (r + s) := by simp [c]
  have hd : HasFDerivAt (chart F.1 g) (fderiv ℝ (chart F.1 g) (oneL E (r + s))) (c 0) := by
    rw [h0]; exact (differentiableAt_chart F.2 g).hasFDerivAt
  have h2 := hd.comp_hasDerivAt (0 : ℝ) hc
  have ev : ∀ (n : ℕ) (Y : Lie E n), ∀ᶠ t : ℝ in 𝓝 0, oneL E n + t • Y ∈ invSet E n := by
    intro n Y
    have hcont : Continuous fun t : ℝ => oneL E n + t • Y := by fun_prop
    refine hcont.continuousAt.eventually_mem (isOpen_invSet.mem_nhds ?_)
    simp only [zero_smul, add_zero]
    change IsUnit (Matrix.of (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) (Cinf E))))
    rw [Equiv.apply_symm_apply]
    exact isUnit_one
  have hz : (chart F.1 g ∘ c) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [ev r (toL X₁), ev s (toL X₂)] with t h1 h2
    obtain ⟨u₁, hu₁⟩ := h1
    obtain ⟨u₂, hu₂⟩ := h2
    have e : c t = toL (lev (Cinf E) r s (u₁, u₂)).val := by
      rw [val_lev]
      change c t = toL (blockM u₁.val u₂.val)
      rw [hu₁, hu₂]
      exact one_add_smul_blockM t X₁ X₂
    rw [Function.comp_apply, e, chart_val, infGL_lev, hg, ← map_mul]
    exact hF _
  exact h2.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)

variable (E r s) in

def vanAlg : Subalgebra ℂ (Module.End ℂ (Sm E (r + s))) where
  carrier := {z | ∀ F : Sm E (r + s), (∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0) →
    ∀ m : GA E r × GA E s, (z F).1 (lev (Ad E) r s m) = 0}
  mul_mem' hx hy F hF := hx _ (hy F hF)
  add_mem' {x y} hx hy F hF m := by
    change (x F).1 _ + (y F).1 _ = 0
    rw [hx F hF m, hy F hF m, add_zero]
  algebraMap_mem' c F hF m := by
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hF m, smul_zero]

theorem Eop_mem_of {a : ℕ} (S : Subalgebra ℂ (Module.End ℂ (Sm E a))) (τ : E →+* ℂ) (p q : Fin a)
    (h : ∀ x, lieS E a p q x ∈ S) : Eop τ p q ∈ S :=
  S.smul_mem (S.sub_mem (h _) (S.smul_mem (h _) _)) _

theorem lie_block_mem (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) :
    lie E (r + s) (toL (blockM X₁ X₂)) ∈ vanAlg E r s :=
  fun _ hF m => lieD_block hF X₁ X₂ m

theorem single_castAdd (i j : Fin r) (x : Cinf E) :
    Matrix.single (Fin.castAdd s i) (Fin.castAdd s j) x = blockM (Matrix.single i j x) (0 : Matrix (Fin s) (Fin s) (Cinf E)) := by
  have hc : ∀ k : Fin r, Fin.castAdd s k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl k) := fun k => Fin.ext (by simp)
  have hn : ∀ k : Fin s, Fin.natAdd r k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr k) := fun k => Fin.ext (by simp)
  rw [hc, hc]
  ext a b
  obtain ⟨a, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective a
  obtain ⟨b, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective b
  simp only [blockM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.single_apply]

theorem single_natAdd (i j : Fin s) (x : Cinf E) :
    Matrix.single (Fin.natAdd r i) (Fin.natAdd r j) x = blockM (0 : Matrix (Fin r) (Fin r) (Cinf E)) (Matrix.single i j x) := by
  have hc : ∀ k : Fin r, Fin.castAdd s k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl k) := fun k => Fin.ext (by simp)
  have hn : ∀ k : Fin s, Fin.natAdd r k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr k) := fun k => Fin.ext (by simp)
  rw [hn, hn]
  ext a b
  obtain ⟨a, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective a
  obtain ⟨b, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective b
  simp only [blockM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.single_apply]

theorem capR_mem (τ : E →+* ℂ) (u : ℂ) : capR r s τ u ∈ vanAlg E r s :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => by
    rw [lieS_apply, single_castAdd]; exact lie_block_mem _ _) _

theorem capS_mem (τ : E →+* ℂ) (u : ℂ) : capS r s τ u ∈ vanAlg E r s :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => by
    rw [lieS_apply, single_natAdd]; exact lie_block_mem _ _) _

variable (E) in

def nInvAlg (a r : ℕ) : Subalgebra ℂ (Module.End ℂ (Sm E a)) where
  carrier := {z | ∀ ψ : Sm E a, (∀ (x : BlockIx a r → Ad E) (g : GA E a), ψ.1 (unip x * g) = ψ.1 g) →
    ∀ (x : BlockIx a r → Ad E) (g : GA E a), (z ψ).1 (unip x * g) = (z ψ).1 g}
  mul_mem' hx hy ψ hψ := hx _ (hy ψ hψ)
  add_mem' {x y} hx hy ψ hψ v g := by
    change (x ψ).1 _ + (y ψ).1 _ = (x ψ).1 _ + (y ψ).1 _
    rw [hx ψ hψ v g, hy ψ hψ v g]
  algebraMap_mem' c ψ hψ v g := by
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hψ v g]

theorem lie_mem_nInvAlg (a r : ℕ) (X : Lie E a) : lie E a X ∈ nInvAlg E a r := by
  intro ψ hψ v g
  have e : chart ψ.1 (unip v * g) = chart ψ.1 g := by
    funext x
    unfold chart
    split_ifs with hx
    · rw [mul_assoc, hψ v]
    · rfl
  simp only [GlobalTheory.CuspRep.lie_apply, lieD, e]

theorem cap_mem_nInvAlg (a r : ℕ) (τ : E →+* ℂ) (u : ℂ) : cap (a := a) τ u ∈ nInvAlg E a r :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => lie_mem_nInvAlg a r _) _

theorem capStable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ)
    (F : Sm E (r + s)) :
    ((∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0) →
      (∀ m : GA E r × GA E s, (capR r s τ u F).1 (lev (Ad E) r s m) = 0) ∧
        ∀ m : GA E r × GA E s, (capS r s τ u F).1 (lev (Ad E) r s m) = 0) ∧
    ((∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) →
      ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)),
        (cap (a := r + s) τ u F).1 (unip x * g) = (cap (a := r + s) τ u F).1 g) :=
  ⟨fun hF => ⟨capR_mem τ u F hF, capS_mem τ u F hF⟩, fun hF => cap_mem_nInvAlg (r + s) r τ u F hF⟩

end GlobalTheory.CompanionTheory.CTFin.CapStable

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralTorusContractsLowerStatement
section
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_torus_contracts_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ U ∈ 𝓝 (1 : GL (Fin n) k),
    ∃ t : Levi k (fun a => Fin (d a)), (∀ m, t * m = m * t) ∧
      ∀ c ∈ lowC k e, (leviEmb k e t)⁻¹ * c * leviEmb k e t ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract | exact GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract | (intros; apply GlobalTheory.CompanionTheory.MoyPrasad.lowC_central_contract <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartStarInvT
section
open NumberField IsDedekindDomain Topology Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec GlobalTheory.SmGL GlobalTheory.ThetaPull
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.DualAct

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem map_invT {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (invT a R g) = invT a S (GeneralLinearGroup.map p g) := by
  ext i j
  change p (((g⁻¹ : GL (Fin a) R).val) j i) = ((GeneralLinearGroup.map p g)⁻¹ : GL (Fin a) S).val j i
  rw [← map_inv]
  rfl

theorem invT_infGL (y : GL (Fin a) (Cinf E)) :
    invT a (Ad E) (infGL E a y) = infGL E a (invT a (Cinf E) y) :=
  ga_ext (by rw [map_invT, pInf_infGL, pInf_infGL])
    (by rw [map_invT, pFin_infGL, pFin_infGL, map_one])

theorem invT_finGL (k : GL (Fin a) (Af E)) :
    invT a (Ad E) (finGL E a k) = finGL E a (invT a (Af E) k) :=
  ga_ext (by rw [map_invT, pInf_finGL, pInf_finGL, map_one])
    (by rw [map_invT, pFin_finGL, pFin_finGL])

theorem invT_toUnits (k : Kinf E a) :
    invT a (Cinf E) (Unitary.toUnits k) = Unitary.toUnits (barK k) := by
  ext i j
  rfl

omit [IsTotallyComplex E] in
variable (E a) in

def trL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (Matrix.of X)ᵀ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

omit [IsTotallyComplex E] in
theorem trL_apply (X : Lie E a) : trL E a X = toL (Matrix.of X)ᵀ := rfl

omit [IsTotallyComplex E] in

theorem toL_invT (y : GL (Fin a) (Cinf E)) :
    toL (invT a (Cinf E) y).val = trL E a (GlobalTheory.ThetaPull.invL (toL y.val)) := by
  rw [trL_apply, GlobalTheory.ThetaPull.invL]
  change toL ((y⁻¹ : GL (Fin a) (Cinf E)).val)ᵀ = toL (Matrix.of (Matrix.of.symm (Matrix.of.symm y.val |> Matrix.of)⁻¹))ᵀ
  simp [Matrix.coe_units_inv]

theorem chart_star_invT (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => star (φ (invT a (Ad E) g))) g x =
      star (chart φ (invT a (Ad E) g) (trL E a (GlobalTheory.ThetaPull.invL x))) := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [← toL_invT, chart_val, chart_val, map_mul, invT_infGL]

theorem lieD_star_invT (X : Lie E a) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) :
    lieD X (fun g => star (φ (invT a (Ad E) g))) g =
      star (lieD (toL (-(Matrix.of X)ᵀ)) φ (invT a (Ad E) g)) := by
  have e : chart (fun g => star (φ (invT a (Ad E) g))) g =ᶠ[𝓝 (oneL E a)]
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ chart φ (invT a (Ad E) g) ∘ trL E a ∘ GlobalTheory.ThetaPull.invL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_star_invT φ g hx
  have h1 : (trL E a ∘ GlobalTheory.ThetaPull.invL) (oneL E a) = oneL E a :=
    (toL_invT 1).symm.trans (by rw [map_one]; rfl)
  have h2 := HasFDerivAt.comp (oneL E a) (f := trL E a ∘ GlobalTheory.ThetaPull.invL)
    (by rw [h1]; exact (differentiableAt_chart hφ (invT a (Ad E) g)).hasFDerivAt)
    ((trL E a).hasFDerivAt.comp (oneL E a) GlobalTheory.ThetaPull.invL_smooth.2)
  have h3 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp (oneL E a) h2
  unfold lieD
  rw [e.fderiv_eq, h3.fderiv]
  have e2 : toL (-(Matrix.of X)ᵀ) = -(toL (Matrix.of X)ᵀ : Lie E a) := rfl
  simp [trL_apply]
  rw [e2, map_neg, map_neg]

theorem act_star_invT (o : Op E a) (φ ψ χ : Sm E a)
    (hψ : ∀ g, ψ.1 g = star (φ.1 (invT a (Ad E) g)))
    (hχ : ∀ g, χ.1 g = star ((act (invTOp o) φ).1 (invT a (Ad E) g))) :
    act o ψ = χ := by
  refine Subtype.ext <| funext fun g => ?_
  rw [hχ]
  cases o with
  | fin k =>
    change ψ.1 (g * finGL E a k) = star (φ.1 (invT a (Ad E) g * finGL E a (invT a (Af E) k)))
    rw [hψ, map_mul, invT_finGL]
  | cpt k =>
    change ψ.1 (g * infGL E a (Unitary.toUnits k)) =
      star (φ.1 (invT a (Ad E) g * infGL E a (Unitary.toUnits (barK k))))
    rw [hψ, map_mul, invT_infGL, invT_toUnits]
  | lie X =>
    have e : ψ.1 = fun g => star (φ.1 (invT a (Ad E) g)) := funext hψ
    change lieD X ψ.1 g = star (lieD (toL (-(Matrix.of X)ᵀ)) φ.1 (invT a (Ad E) g))
    rw [e, lieD_star_invT X φ.2 g]

end GlobalTheory.CompanionTheory.DualAct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjTwistedCentralizerStatement
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_conj_twisted_centralizer : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ →
  (∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a) →
  (∀ t ∈ twCent (thC n) d, ∀ X ∈ nilrad W₁ W₂, t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂) →
  (∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∀ g : GL (Fin n) ℂ,
    μd {t : twCent (thC n) d | (t : GL (Fin n) ℂ) * g ∈ nSet W₁ W₂ C} ≠ ⊤) →
  ∃ ρ : GL (Fin n) ℂ → ℝ≥0∞, IsQuotNormaliser (twCent (thC n) d) μd ρ ∧
    ∀ (X : nilrad W₁ W₂) (g : GL (Fin n) ℂ), ρ (uOf X * g) = ρ g := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.tNormaliser | exact GlobalTheory.CompanionTheory.LocVan.tNormaliser | (intros; apply GlobalTheory.CompanionTheory.LocVan.tNormaliser <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenExhaustionStabilizes
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BaireCoset

open scoped Pointwise

theorem baire_double_coset : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (P : Subgroup G), IsClosed (P : Set G) → ∀ Kc : Set G, IsCompact Kc → (∀ g, ∃ p ∈ P, ∃ c ∈ Kc, g = p * c) → ∀ L : ℕ → Subgroup G, Monotone L → (∀ j, IsCompact (L j : Set G)) → ∀ (x : G) (S : Set G), IsOpen S → (∀ p ∈ P, ∀ g ∈ S, p * g ∈ S) → IsClosed (S ∩ {g | ∃ p ∈ P, ∃ j, ∃ n ∈ L j, g = p * x * n}) → ∃ j, ∀ g ∈ S, (∃ p ∈ P, ∃ j', ∃ n ∈ L j', g = p * x * n) → ∃ p ∈ P, ∃ n ∈ L j, g = p * x * n := by
  intro G _ _ _ _ _ P hP Kc hKc hcov L hL hLc x S hS hSP hT
  set C : Set G := {g | ∃ p ∈ P, ∃ j, ∃ n ∈ L j, g = p * x * n} with hC
  let A : ℕ → Set G := fun j => {g | ∃ p ∈ P, ∃ n ∈ L j, g = p * x * n}
  have hAmono : ∀ {i j}, i ≤ j → A i ⊆ A j := by
    rintro i j hij g ⟨p, hp, n, hn, rfl⟩
    exact ⟨p, hp, n, hL hij hn, rfl⟩
  have hCA : ∀ g ∈ C, ∃ j, g ∈ A j := by
    rintro g ⟨p, hp, j, n, hn, rfl⟩
    exact ⟨j, p, hp, n, hn, rfl⟩
  have hAclosed : ∀ j, IsClosed (A j) := by
    intro j
    have hc : IsCompact ((fun n : G => x * n) '' (L j : Set G)) :=
      (hLc j).image (continuous_const.mul continuous_id)
    have hEq : A j = (P : Set G) * ((fun n : G => x * n) '' (L j : Set G)) := by
      ext g
      constructor
      · rintro ⟨p, hp, n, hn, rfl⟩
        exact Set.mem_mul.2 ⟨p, hp, x * n, ⟨n, hn, rfl⟩, (mul_assoc _ _ _).symm⟩
      · intro h
        obtain ⟨p, hp, _, ⟨n, hn, rfl⟩, rfl⟩ := Set.mem_mul.1 h
        exact ⟨p, hp, n, hn, (mul_assoc _ _ _).symm⟩
    rw [hEq]
    exact hP.mul_right_of_isCompact hc
  have hCP : ∀ p ∈ P, ∀ g ∈ C, p * g ∈ C := by
    rintro p hp g ⟨q, hq, j, n, hn, rfl⟩
    exact ⟨p * q, P.mul_mem hp hq, j, n, hn, by simp only [mul_assoc]⟩
  have hCL : ∀ j, ∀ m ∈ L j, ∀ g ∈ C, g * m ∈ C := by
    rintro j m hm g ⟨q, hq, i, n, hn, rfl⟩
    exact ⟨q, hq, max i j, n * m,
      (L (max i j)).mul_mem (hL (le_max_left i j) hn) (hL (le_max_right i j) hm),
      by simp only [mul_assoc]⟩
  by_cases hne : (S ∩ C).Nonempty
  · haveI : Nonempty ↥(S ∩ C) := hne.to_subtype
    haveI : LocallyCompactSpace ↥(S ∩ C) := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
    obtain ⟨j0, y, hy⟩ := nonempty_interior_of_iUnion_of_closed
      (f := fun j => ((↑) : ↥(S ∩ C) → G) ⁻¹' A j)
      (fun j => (hAclosed j).preimage continuous_subtype_val)
      (by
        refine Set.eq_univ_of_forall fun t => ?_
        obtain ⟨j, hj⟩ := hCA t t.2.2
        exact Set.mem_iUnion.2 ⟨j, hj⟩)
    obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.1
      (isOpen_interior (s := ((↑) : ↥(S ∩ C) → G) ⁻¹' A j0))
    have hyV : (y : G) ∈ V := by
      have h : y ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' V := by rw [hVeq]; exact hy
      exact h
    have hVA : ∀ g ∈ V, g ∈ S → g ∈ C → g ∈ A j0 := by
      intro g hgV hgS hgC
      have h : (⟨g, hgS, hgC⟩ : ↥(S ∩ C)) ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' V := hgV
      rw [hVeq] at h
      have h2 : (⟨g, hgS, hgC⟩ : ↥(S ∩ C)) ∈ ((↑) : ↥(S ∩ C) → G) ⁻¹' A j0 := interior_subset h
      exact h2
    obtain ⟨p, hp, n, hn, hyeq⟩ := hVA y hyV y.2.1 y.2.2
    let V₁ : Set G := (fun g => p * g * n) ⁻¹' (V ∩ S)
    have hV₁o : IsOpen V₁ :=
      (hV.inter hS).preimage ((continuous_const.mul continuous_id).mul continuous_const)
    have hxV₁ : x ∈ V₁ := by
      show p * x * n ∈ V ∩ S
      rw [← hyeq]
      exact ⟨hyV, y.2.1⟩
    have hnL : ∀ g ∈ V₁, g ∈ C → g ∈ A j0 := by
      intro g hgV hgC
      obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hVA (p * g * n) hgV.1 hgV.2 (hCL j0 n hn _ (hCP p hp g hgC))
      refine ⟨p⁻¹ * p₂, P.mul_mem (P.inv_mem hp) hp₂, n₂ * n⁻¹,
        (L j0).mul_mem hn₂ ((L j0).inv_mem hn), ?_⟩
      calc g = p⁻¹ * (p * g * n) * n⁻¹ := by group
        _ = p⁻¹ * (p₂ * x * n₂) * n⁻¹ := by rw [e]
        _ = p⁻¹ * p₂ * x * (n₂ * n⁻¹) := by group
    let O : ℕ → Set G := fun j => ⋃₀ {W | IsOpen W ∧ W ∩ C ⊆ A j}
    have hOo : ∀ j, IsOpen (O j) := fun j => isOpen_sUnion fun W hW => hW.1
    have hOm : Monotone O := fun i j hij =>
      Set.sUnion_subset_sUnion fun W hW => ⟨hW.1, hW.2.trans (hAmono hij)⟩
    have hOA : ∀ j, O j ∩ C ⊆ A j := by
      rintro j g ⟨⟨W, hW, hgW⟩, hgC⟩
      exact hW.2 ⟨hgW, hgC⟩
    have hAO : ∀ j, j0 ≤ j → A j ⊆ O j := by
      rintro j hj _ ⟨p', hp', m, hm, rfl⟩
      refine ⟨(fun g => p'⁻¹ * g * m⁻¹) ⁻¹' V₁,
        ⟨hV₁o.preimage ((continuous_const.mul continuous_id).mul continuous_const), ?_⟩, ?_⟩
      · rintro g ⟨hgW, hgC⟩
        have hu : p'⁻¹ * g * m⁻¹ ∈ C :=
          hCL j _ ((L j).inv_mem hm) _ (hCP _ (P.inv_mem hp') g hgC)
        have hu' : p'⁻¹ * g * m⁻¹ ∈ A j := hAmono hj (hnL _ hgW hu)
        obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hu'
        refine ⟨p' * p₂, P.mul_mem hp' hp₂, n₂ * m, (L j).mul_mem hn₂ hm, ?_⟩
        calc g = p' * (p'⁻¹ * g * m⁻¹) * m := by group
          _ = p' * (p₂ * x * n₂) * m := by rw [e]
          _ = p' * p₂ * x * (n₂ * m) := by group
      · show p'⁻¹ * (p' * x * m) * m⁻¹ ∈ V₁
        have : p'⁻¹ * (p' * x * m) * m⁻¹ = x := by group
        rw [this]
        exact hxV₁
    obtain ⟨i, hi⟩ := (hKc.inter_right hT).elim_directed_cover O hOo
      (by
        rintro g ⟨_, hgS, hgC⟩
        obtain ⟨j, hj⟩ := hCA g hgC
        exact Set.mem_iUnion.2 ⟨max j j0,
          hAO _ (le_max_right j j0) (hAmono (le_max_left j j0) hj)⟩)
      hOm.directed_le
    refine ⟨i, fun g hgS hgC => ?_⟩
    obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
    have hcS : c ∈ S := by
      have := hSP q⁻¹ (P.inv_mem hq) _ hgS
      rwa [inv_mul_cancel_left] at this
    have hcC : c ∈ C := by
      have := hCP q⁻¹ (P.inv_mem hq) _ hgC
      rwa [inv_mul_cancel_left] at this
    obtain ⟨p₂, hp₂, n₂, hn₂, e⟩ := hOA i ⟨hi ⟨hc, hcS, hcC⟩, hcC⟩
    exact ⟨q * p₂, P.mul_mem hq hp₂, n₂, hn₂, by rw [e]; simp only [mul_assoc]⟩
  · refine ⟨0, fun g hgS hgC => ?_⟩
    exact absurd ⟨g, hgS, hgC⟩ hne

end GlobalTheory.CompanionTheory.BaireCoset
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermKFiniteCoefficientStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_k_finite_coefficient : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.KType.ct_mem_coeffSpan | exact GlobalTheory.CompanionTheory.CTFin.KType.ct_mem_coeffSpan | (intros; apply GlobalTheory.CompanionTheory.CTFin.KType.ct_mem_coeffSpan <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLeviParabolicFormulaStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_levi_parabolic_formula : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (φ : Sm E (r + s)), (∀ (γ : GL (Fin (r + s)) E) (g : GA E (r + s)), φ.1 (ratGL E (r + s) γ * g) = φ.1 g) → IsOpen {k | finRep E (r + s) k φ = φ} → ∀ [MeasurableSpace (BlockIx (r + s) r → Ad E)] [BorelSpace (BlockIx (r + s) r → Ad E)] (μ : Measure (BlockIx (r + s) r → Ad E)) (𝓕 : Set (BlockIx (r + s) r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E (r + s) r) 𝓕 μ → ∀ (γ : GL (Fin r) E × GL (Fin s) E) (g : GA E (r + s)), ∫ x in 𝓕, φ.1 (unip x * (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g)) ∂μ = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.integral_unip_lev_mul | exact GlobalTheory.CompanionTheory.CTFin.integral_unip_lev_mul | (intros; apply GlobalTheory.CompanionTheory.CTFin.integral_unip_lev_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermTranslateFormulaStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_translate_formula : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ (y : BlockIx a r → Ad E) (g : GA E a), ∫ x in 𝓕, φ.1 (unip x * (unip y * g)) ∂μ = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.constTerm_unip_left | exact GlobalTheory.CompanionTheory.CTFin.constTerm_unip_left | (intros; apply GlobalTheory.CompanionTheory.CTFin.constTerm_unip_left <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DropHom
section
noncomputable section

open GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.FineProd

variable {k : Type} [Field k]

def dropHom {r r' : ℕ} (d : Fin r → ℕ) (o : Fin r' → Fin r) :
    Levi k (fun j => Fin (d j)) →* Levi k (fun a => Fin (d (o a))) where
  toFun g a := g (o a)
  map_one' := rfl
  map_mul' _ _ := rfl

end GlobalTheory.CompanionTheory.FineProd

end
end

