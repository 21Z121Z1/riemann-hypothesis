import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0310
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0307
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0333
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeGaussianSumOfLengthEqTsumStabilizerCosets
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0302
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0331

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsSameRationalInnerClassAreTranslates
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.CntC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gmap_mul (a b : GV D) (M : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem gmap_one (M : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) M = M := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem gmap_inv_of {a : GV D} {M N : LV D} (h : Formalism.HermitianLatticesTheory.gmap a M = N) : Formalism.HermitianLatticesTheory.gmap a⁻¹ N = M := by
  rw [← h, ← gmap_mul, inv_mul_cancel, gmap_one]

theorem adapt_mul {T : D.host.E} {F G H : LFlag (VS D) D.R.rS T} {g g' : GV D} (hg : Adapt g F G)
    (hg' : Adapt g' G H) : Adapt (g' * g) F H := by
  refine ⟨mul_mem hg'.1 hg.1, fun a => ?_⟩
  have hmap := (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D T G H g' hg').1 a.val
  have h1 : g' (g (frame F a) - frame G a) ∈ Xflag H a.val := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem (hg.2 a)
  have h2 := hg'.2 a
  have e : (g' * g) (frame F a) - frame H a =
      g' (g (frame F a) - frame G a) + (g' (frame G a) - frame H a) := by
    rw [map_sub, LinearEquiv.mul_apply]
    abel
  rw [e]
  exact add_mem h1 h2

theorem adapt_fix {T : D.host.E} {F : LFlag (VS D) D.R.rS T} {h : GV D} (hi : h ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hf : ∀ a, h (frame F a) = frame F a) : Adapt h F F := by
  refine ⟨hi, fun a => ?_⟩
  rw [hf a, sub_self]
  exact zero_mem _

theorem frame_mapLF {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {γ : GV D} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (a : Fin (D.R.rS + 1)) : frame (mapLF γ F) a = γ (frame F a) := by
  simp only [frame, mapLF, dif_pos hγ, Formalism.MainNotions.S.FlagG.fvec]
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Fin.snoc_last]
    rfl
  · simp only [Fin.snoc_castSucc]
    rfl

theorem xsp_mapLF {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {γ : GV D} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    Xsp (mapLF γ F) = (Xsp F).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  simp only [Xsp, mapLF, dif_pos hγ, Formalism.MainNotions.S.FlagG.X, Submodule.map_span, ← Set.range_comp]
  rfl

theorem adapt_mapLF {T : D.host.E} {F G : LFlag (VS D) D.R.rS T} {γ g : GV D}
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) : Adapt g (mapLF γ F) G ↔ Adapt (g * γ) F G := by
  simp only [Adapt, frame_mapLF F hγ, LinearEquiv.mul_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨mul_mem h1 hγ, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := mul_mem h1 (inv_mem hγ)
    rwa [mul_inv_cancel_right] at this

end GlobalTheory.Unfold.CntC

namespace GlobalTheory.Unfold.CntC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem translates : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ t : TauC Y u u') (Λ₀ Λ₁ : LV D), TG F F' t₀ Λ₀ → TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → t.lam = t₀.lam ∧ t.lam' = t₀.lam' ∧ ∃ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam, ∃ a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam', KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t₀.lam (a * t₀.lin * a'⁻¹) t.lin := by
  intro D X Y u u' F F' w _ _ t₀ t Λ₀ Λ₁ h₀ h₁ hR
  obtain ⟨g₀, hg₀a, hg₀b, rfl⟩ := h₀
  obtain ⟨ψ₁, hψ₁a, hψ₁b, rfl⟩ := h₁
  obtain ⟨h, ⟨hhi, hhF, hhF'⟩, hgd⟩ := hR
  rw [← gmap_mul] at hgd
  set ψ₀ := h * g₀ with hψ₀
  have hψ₀a : Adapt ψ₀ (lf D (X.Fu u)) F := adapt_mul hg₀a (adapt_fix hhi hhF)
  have hψ₀b : Adapt ψ₀ t₀.frame F' := adapt_mul hg₀b (adapt_fix hhi hhF')
  have li₀ : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have lg₀ : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have li : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have lg : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  have e1 : Lsub (Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam) F = Lsub (Formalism.HermitianLatticesTheory.gmap ψ₁ t.lam) F := congrArg Prod.fst hgd
  have e2 : Lsub (Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam) F' = Lsub (Formalism.HermitianLatticesTheory.gmap ψ₁ t.lam) F' :=
    congrArg (fun x => x.2.1) hgd
  have e3 : (gdat F F' (Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam)).2.2 = (gdat F F' (Formalism.HermitianLatticesTheory.gmap ψ₁ t.lam)).2.2 :=
    congrArg (fun x => x.2.2) hgd
  obtain ⟨hlam, n, hn, hA⟩ := GlobalTheory.T.rowLattices_eq_of_adaptedIsometry_innerLattices_eq D X Y u F ψ₀ ψ₁ t₀.lam t.lam t₀.mem t.mem hψ₀a hψ₁a e1
  have hψ₀b' : Adapt (ψ₀ * t₀.lin) (lf D (X.Fu u')) F' :=
    (adapt_mapLF (F := lf D (X.Fu u')) (G := F') (g := ψ₀) li₀).1 hψ₀b
  have hψ₁b' : Adapt (ψ₁ * t.lin) (lf D (X.Fu u')) F' :=
    (adapt_mapLF (F := lf D (X.Fu u')) (G := F') (g := ψ₁) li).1 hψ₁b
  have q₀ : Formalism.HermitianLatticesTheory.gmap (ψ₀ * t₀.lin) t₀.lam' = Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam :=
    (gmap_mul ψ₀ t₀.lin t₀.lam').trans (congrArg (Formalism.HermitianLatticesTheory.gmap ψ₀) lg₀)
  have q₁ : Formalism.HermitianLatticesTheory.gmap (ψ₁ * t.lin) t.lam' = Formalism.HermitianLatticesTheory.gmap ψ₁ t.lam :=
    (gmap_mul ψ₁ t.lin t.lam').trans (congrArg (Formalism.HermitianLatticesTheory.gmap ψ₁) lg)
  have e2' : Lsub (Formalism.HermitianLatticesTheory.gmap (ψ₀ * t₀.lin) t₀.lam') F' = Lsub (Formalism.HermitianLatticesTheory.gmap (ψ₁ * t.lin) t.lam') F' := by
    rw [q₀, q₁]
    exact e2
  obtain ⟨hlam', n', hn', hA'⟩ :=
    GlobalTheory.T.rowLattices_eq_of_adaptedIsometry_innerLattices_eq D X Y u' F' (ψ₀ * t₀.lin) (ψ₁ * t.lin) t₀.lam' t.lam' t₀.mem' t.mem' hψ₀b' hψ₁b' e2'
  refine ⟨hlam, hlam', n * (ψ₁⁻¹ * ψ₀), hA, n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin)), hA', ?_⟩
  have hA2 : Formalism.HermitianLatticesTheory.gmap (n * (ψ₁⁻¹ * ψ₀)) t₀.lam = t₀.lam := hA.2
  have hA'2 : Formalism.HermitianLatticesTheory.gmap (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) t₀.lam' = t₀.lam' := hA'.2
  have hγ : n * (ψ₁⁻¹ * ψ₀) * t₀.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin)))⁻¹ = n * t.lin * n'⁻¹ := by
    group
  have hβ : t.lin * (n * t.lin * n'⁻¹)⁻¹ =
      t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹ * (n * (ψ₁⁻¹ * ψ₀))⁻¹ := by
    group
  rw [hγ]
  have hnN := GlobalTheory.T.rationalUnipotent_frameAdapted_and_inv_mem D _ _ n hn
  have hn'N := GlobalTheory.T.rationalUnipotent_frameAdapted_and_inv_mem D _ _ n' hn'
  have hn'iN := GlobalTheory.T.rationalUnipotent_frameAdapted_and_inv_mem D _ _ n'⁻¹ hn'N.2
  have hni : n⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hnN.2.1
  have hn'i : n'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hn'N.2.1
  have hni' : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hn.1
  have hγi : n * t.lin * n'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (mul_mem hni' li) hn'i
  unfold KeyEq
  refine ⟨⟨n⁻¹, hnN.2, n', hn', by group⟩, ?_⟩
  have hΨ₀a : Adapt (ψ₁ * n⁻¹) (lf D (X.Fu u)) F := adapt_mul (GlobalTheory.T.rationalUnipotent_frameAdapted_and_inv_mem D _ _ n⁻¹ hnN.2).1 hψ₁a
  have hΨ₀b : Adapt (ψ₁ * n⁻¹) (mapLF (n * t.lin * n'⁻¹) (lf D (X.Fu u'))) F' := by
    refine (adapt_mapLF (F := lf D (X.Fu u')) (G := F') (g := ψ₁ * n⁻¹) hγi).2 ?_
    have : ψ₁ * n⁻¹ * (n * t.lin * n'⁻¹) = ψ₁ * t.lin * n'⁻¹ := by group
    have key := adapt_mul hn'iN.1 hψ₁b'
    rw [← this] at key
    exact key
  have hg1 : Formalism.HermitianLatticesTheory.gmap (ψ₁ * n⁻¹) t₀.lam = Formalism.HermitianLatticesTheory.gmap ψ₀ t₀.lam := by
    have : ψ₁ * n⁻¹ = ψ₀ * (n * (ψ₁⁻¹ * ψ₀))⁻¹ := by group
    rw [this, gmap_mul, gmap_inv_of hA2]
  refine GlobalTheory.T.innerLatticeIdentification_compat_of_graph_eq D _ _ (lf D (X.Fu u)) F (mapLF (n * t.lin * n'⁻¹) (lf D (X.Fu u')))
    (mapLF t.lin (lf D (X.Fu u'))) F' t₀.lam (ψ₁ * n⁻¹) ψ₁ (t.lin * (n * t.lin * n'⁻¹)⁻¹)
    (mul_mem hψ₁a.1 hni) hψ₁a.1 (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D _ _ _ _ hΨ₀a).2 (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D _ _ _ _ hψ₁a).2
    (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D _ _ _ _ hΨ₀b).2 (GlobalTheory.T.frameAdaptedIsometry_map_flagSpaces D _ (mapLF t.lin (lf D (X.Fu u'))) F' ψ₁ hψ₁b).2
    ?_ (mul_mem li (inv_mem hγi)) ?_ ?_ ?_ ?_
  · exact (congrArg (fun Λ => (gdat F F' Λ).2.2) hg1).trans
      (e3.trans (congrArg (fun Λ => (gdat F F' (Formalism.HermitianLatticesTheory.gmap ψ₁ Λ)).2.2) hlam))
  · calc Formalism.HermitianLatticesTheory.gmap (t.lin * (n * t.lin * n'⁻¹)⁻¹) t₀.lam
          = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹ * (n * (ψ₁⁻¹ * ψ₀))⁻¹) t₀.lam :=
            congrArg (fun g => Formalism.HermitianLatticesTheory.gmap g t₀.lam) hβ
      _ = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹) (Formalism.HermitianLatticesTheory.gmap (n * (ψ₁⁻¹ * ψ₀))⁻¹ t₀.lam) := gmap_mul _ _ _
      _ = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹) t₀.lam :=
            congrArg (Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) * t₀.lin⁻¹)) (gmap_inv_of hA2)
      _ = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin)))) (Formalism.HermitianLatticesTheory.gmap t₀.lin⁻¹ t₀.lam) := gmap_mul _ _ _
      _ = Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin)))) t₀.lam' :=
            congrArg (Formalism.HermitianLatticesTheory.gmap (t.lin * (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))))) (gmap_inv_of lg₀)
      _ = Formalism.HermitianLatticesTheory.gmap t.lin (Formalism.HermitianLatticesTheory.gmap (n' * ((ψ₁ * t.lin)⁻¹ * (ψ₀ * t₀.lin))) t₀.lam') := gmap_mul _ _ _
      _ = Formalism.HermitianLatticesTheory.gmap t.lin t₀.lam' := congrArg (Formalism.HermitianLatticesTheory.gmap t.lin) hA'2
      _ = t₀.lam := (congrArg (Formalism.HermitianLatticesTheory.gmap t.lin) hlam'.symm).trans (lg.trans hlam)
  · rw [xsp_mapLF _ hγi, xsp_mapLF _ li, ← Submodule.map_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    exact congrArg (fun g : GV D => g x) (inv_mul_cancel_right t.lin (n * t.lin * n'⁻¹))
  · intro l hl
    have : ψ₁⁻¹ * (ψ₁ * n⁻¹) = n⁻¹ := by group
    have key := hnN.2.2.2 l (Submodule.mem_inf.mp hl).2
    rw [← this] at key
    exact key
  · intro x' hx'
    have : ψ₁⁻¹ * (ψ₁ * n⁻¹) = n⁻¹ := by group
    have key := GlobalTheory.T.unipotent_right_change_moves_flag_complement D _ (lf D (X.Fu u')) (n * t.lin * n'⁻¹) t.lin n⁻¹ n' hγi hni hn' (by group) x'
      (Submodule.mem_inf.mp hx').2
    rw [← this] at key
    exact key

end GlobalTheory.Unfold.CntC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaCocycleProductOfRationalUnipotentsStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_cocycle_product_of_rational_unipotents : ∀ (D : D7) {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F : LFlag (VS D) D.R.rS T) (F' F'' : LFlag (VS D) D.R.rS T'), Submodule.IsLattice D.host.E Λ → F.zt = F.fl.z → F'.zt = F'.fl.z → F''.zt = F''.fl.z → ∀ n ∈ NRat F, ∀ m ∈ NRat F', (∀ a, frame F'' a = (n * m) (frame F' a)) → Th Λ F F' F'' (n * m) = Hp Λ F F' := by
  first | exact @GlobalTheory.DcosetCompl.th_eq_hp | exact GlobalTheory.DcosetCompl.th_eq_hp | (intros; apply GlobalTheory.DcosetCompl.th_eq_hp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeBoundedBelowUnipotentRa
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem one_le_rank_of_isIsot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) :
    1 ≤ I.n := by
  by_contra h
  have h0 : I.n = 0 := by omega
  haveI : IsEmpty (Fin I.n) := by rw [h0]; infer_instance
  exact hW.1 (Subsingleton.elim _ _)

theorem exists_pos_le_tau1_mul_of_mem_NA_of_isIsot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (x : I.GA)
    (hW : I.IsIsot W) : ∃ c : ℝ, 0 < c ∧ ∀ m ∈ I.NA W, c ≤ tau1 I (m * x) := by
  obtain ⟨hpos, hcont, hinv, -⟩ := GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties I (one_le_rank_of_isIsot I W hW)
  obtain ⟨-, -, -, -, Cp, hCp, -, hcov⟩ := GlobalTheory.UnipApprox.strong_approximation I W hW
  have hc : Continuous fun y : I.GA => tau1 I (y * x) := hcont.comp (continuous_id.mul continuous_const)
  have key : ∀ m ∈ I.NA W, ∃ y ∈ Cp, tau1 I (m * x) = tau1 I (y * x) := by
    intro m hm
    obtain ⟨γ, hγ, hy⟩ := hcov m hm
    refine ⟨γ⁻¹ * m, hy, ?_⟩
    rw [← hinv γ hγ.1 (γ⁻¹ * m * x)]
    congr 1
    group
  rcases Cp.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun m hm => ?_⟩
    obtain ⟨y, hy, -⟩ := key m hm
    rw [he] at hy
    exact hy.elim
  · obtain ⟨y₀, -, hmin⟩ := hCp.exists_isMinOn hne hc.continuousOn
    refine ⟨tau1 I (y₀ * x), hpos _, fun m hm => ?_⟩
    obtain ⟨y, hy, e⟩ := key m hm
    rw [e]
    exact hmin hy

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGaugeVolumeLeClassNumberDefinite
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.DefiniteVolume

variable (I : AutInst)

theorem eps_eq {r : ℕ} (h : HasSig I r 0) (v : InfinitePlace I.F) : I.ε v = allPos I.n := by
  funext a
  have h0 := (h v).2
  unfold AutInst.qAt at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  have ha := h0 (Finset.mem_univ a)
  simp only [allPos]
  revert ha
  cases I.ε v a <;> simp

theorem rank_eq {r : ℕ} (h : HasSig I r 0) : r = I.n := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  have hp := (h v).1
  rw [AutInst.pAt, eps_eq I h v] at hp
  simpa [allPos] using hp.symm

theorem card_places : Fintype.card (InfinitePlace I.F) = I.f := by
  haveI := I.cm.totReal
  have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at h2
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, AutInst.f]
  omega

theorem pos_at (v : InfinitePlace I.F) (hv : I.ε v = allPos I.n) (y : Fin I.n → I.E) (hy : y ≠ 0) :
    0 < (I.φ v (star y ⬝ᵥ (I.J *ᵥ y))).re := by
  have hconj : ∀ a, I.φ v (star a) = starRingEnd ℂ (I.φ v a) := fun a => I.cm.cmUnram.2.1 (I.φ v) a
  have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hspec : (I.P v)ᴴ * I.J.map (I.φ v) * I.P v = 1 := by
    rw [I.P_spec v, hv, GlobalTheory.UnitaryVolume.Jm_allPos]
  have hmap : I.φ v (star y ⬝ᵥ (I.J *ᵥ y)) =
      star (fun i => I.φ v (y i)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ fun i => I.φ v (y i)) := by
    simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, hconj, Matrix.map_apply,
      starRingEnd_apply]
  have hne : (fun i => I.φ v (y i)) ≠ 0 := by
    intro h0
    apply hy
    funext i
    exact (I.φ v).injective (by simpa using congrFun h0 i)
  rw [hmap]
  generalize (fun i => I.φ v (y i)) = w at hne ⊢
  have hwz : w = I.P v *ᵥ ((I.P v)⁻¹ *ᵥ w) := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  have hz0 : (I.P v)⁻¹ *ᵥ w ≠ 0 := by
    intro h0
    apply hne
    rw [hwz, h0, mulVec_zero]
  rw [hwz, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hspec, one_mulVec]
  exact (Complex.pos_iff.1 (Matrix.dotProduct_star_self_pos_iff.2 hz0)).1

theorem pos_all {r : ℕ} (h : HasSig I r 0) (φ : I.E →+* ℂ) (y : Fin I.n → I.E) (hy : y ≠ 0) :
    0 < (φ (star y ⬝ᵥ (I.J *ᵥ y))).re := by
  have hJ : I.Jᴴ = I.J := by rw [← GlobalTheory.StabCosets.cT_star]; exact I.J_herm
  have hstar : star (star y ⬝ᵥ (I.J *ᵥ y)) = star y ⬝ᵥ (I.J *ᵥ y) := by
    rw [← star_dotProduct_star, star_star, star_mulVec, ← dotProduct_mulVec, hJ]
  obtain ⟨b, hb⟩ := (I.cm.fixed _).1 hstar
  haveI := I.cm.totReal
  have hreal : (InfinitePlace.mk (φ.comp (algebraMap I.F I.E))).IsReal :=
    NumberField.IsTotallyReal.isReal _
  have hemb := NumberField.InfinitePlace.embedding_mk_eq_of_isReal
    (NumberField.InfinitePlace.isReal_mk_iff.1 hreal)
  have hval : φ (star y ⬝ᵥ (I.J *ᵥ y)) =
      I.φ (InfinitePlace.mk (φ.comp (algebraMap I.F I.E))) (star y ⬝ᵥ (I.J *ᵥ y)) := by
    rw [← hb, I.φ_over, hemb]
    rfl
  rw [hval]
  exact pos_at I _ (eps_eq I h _) y hy

theorem hform_eq (z x : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J z x = star z ⬝ᵥ (I.J *ᵥ x) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, starRingEnd_apply, Pi.star_apply,
    mul_assoc]

abbrev DefLat (E : Type) [Field E] [NumberField E] [StarRing E] (r : ℕ) : Type :=
  {X : Matrix (Fin r) (Fin r) E × Submodule (𝓞 E) (Fin r → E) //
      X.1ᴴ = X.1 ∧ (∀ (φ : E →+* ℂ) (y : Fin r → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (X.1 *ᵥ y))).re) ∧
      Submodule.IsLattice E X.2 ∧
      ∀ x, x ∈ X.2 ↔ ∀ y ∈ X.2, star y ⬝ᵥ (X.1 *ᵥ x) ∈ (algebraMap (𝓞 E) E).range}

abbrev Isom (E : Type) [Field E] [NumberField E] [StarRing E] (r : ℕ) (X Y : DefLat E r) : Prop :=
  ∃ γ : GL (Fin r) E, (γ : Matrix (Fin r) (Fin r) E)ᴴ * Y.1.1 * (γ : Matrix (Fin r) (Fin r) E) = X.1.1 ∧
      ∀ y, (γ : Matrix (Fin r) (Fin r) E) *ᵥ y ∈ Y.1.2 ↔ y ∈ X.1.2

theorem isom_equivalence (E : Type) [Field E] [NumberField E] [StarRing E] (r : ℕ) :
    Equivalence (Isom E r) where
  refl X := ⟨1, by simp, fun y => by simp⟩
  symm := by
    rintro X Y ⟨γ, h1, h2⟩
    refine ⟨γ⁻¹, ?_, fun y => ?_⟩
    · have hu : (γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1 := by
        simp
      calc ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᴴ * X.1.1 *
            ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
          = ((γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E))ᴴ * Y.1.1 *
              ((γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) := by
            rw [← h1, conjTranspose_mul]
            simp only [Matrix.mul_assoc]
        _ = Y.1.1 := by rw [hu]; simp
    · have h3 := h2 (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y)
      rw [mulVec_mulVec, Units.mul_inv, one_mulVec] at h3
      exact h3.symm
  trans := by
    rintro X Y Z ⟨γ, h1, h2⟩ ⟨δ, h3, h4⟩
    refine ⟨δ * γ, ?_, fun y => ?_⟩
    · rw [Units.val_mul, conjTranspose_mul, ← h1, ← h3]
      simp only [Matrix.mul_assoc]
    · rw [Units.val_mul, ← mulVec_mulVec, h4, h2]

def latOf {r : ℕ} (h : HasSig I r 0) (x : I.GA) : DefLat I.E I.n :=
  ⟨(I.J, lamX I x), by rw [← GlobalTheory.StabCosets.cT_star]; exact I.J_herm, pos_all I h,
    ⟨(GlobalTheory.PointLattice.lamX_selfDual I x).2.1, (GlobalTheory.PointLattice.lamX_selfDual I x).2.2.1⟩,
    fun y => by
      simpa only [hform_eq] using (GlobalTheory.PointLattice.lamX_selfDual I x).2.2.2.1 y⟩

theorem coset_of_isom {r : ℕ} (h : HasSig I r 0) (x y : I.GA)
    (e : Isom I.E I.n (latOf I h y) (latOf I h x)) :
    ∃ a ∈ I.GFset, x.2⁻¹ * (a * y).2 ∈ I.Kset := by
  obtain ⟨γ, h1, h2⟩ := e
  change (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * γ = I.J at h1
  change ∀ z, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z ∈ lamX I x ↔ z ∈ lamX I y at h2
  have hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := by
    show Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γ = I.J
    rw [GlobalTheory.StabCosets.cT_star]
    exact h1
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.StabCosets.exists_isImage I γ hγ
  refine ⟨a, ⟨γ, hγ, ha1, ha2⟩, ?_⟩
  have hl : lamX I (a * y) = lamX I x := by
    rw [(GlobalTheory.PointEquivariance.equivariance I y γ a hγ ha1 ha2).1]
    ext z
    simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.toLin'_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (h2 u).2 hu
    · intro hz
      refine ⟨((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z, (h2 _).1 ?_, ?_⟩
      · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
        exact hz
      · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  exact (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I x (x⁻¹ * (a * y))).2 (by rw [mul_inv_cancel_left]; exact hl)

theorem covol_le {r : ℕ} (h : HasSig I r 0) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
    [Fintype (Quot (Isom I.E I.n))] :
    covol I.GFset (I.muA μf) Set.univ ≤
      (∏ v, Formalism.REAL.muG (I.ε v) Set.univ) * (Fintype.card (Quot (Isom I.E I.n)) * μf I.Kset) := by
  classical
  let pt : Quot (Isom I.E I.n) → I.GA := fun q =>
    if hq : ∃ x, Quot.mk (Isom I.E I.n) (latOf I h x) = q then hq.choose else 1
  let D : Quot (Isom I.E I.n) → Set I.GA := fun q =>
    Set.univ ×ˢ ((fun g => (pt q).2⁻¹ * g) ⁻¹' I.Kset)
  have hKo : IsOpen I.Kset := (GlobalTheory.adelicStab_isCompact_isOpen I).2.1
  have hDm : ∀ q, MeasurableSet (D q) := fun q =>
    MeasurableSet.univ.prod (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hcover : ∀ z ∈ (Set.univ : Set I.GA), ∃ γ ∈ I.GFset, γ * z ∈ ⋃ q, D q := by
    intro z _
    have hq : ∃ x, Quot.mk (Isom I.E I.n) (latOf I h x) = Quot.mk (Isom I.E I.n) (latOf I h z) :=
      ⟨z, rfl⟩
    have hpt : pt (Quot.mk (Isom I.E I.n) (latOf I h z)) = hq.choose := dif_pos hq
    have e : Isom I.E I.n (latOf I h z) (latOf I h hq.choose) :=
      (isom_equivalence I.E I.n).symm
        ((Equivalence.eqvGen_iff (isom_equivalence I.E I.n)).1 (Quot.eqvGen_exact hq.choose_spec))
    obtain ⟨a, ha, hk⟩ := coset_of_isom I h hq.choose z e
    refine ⟨a, ha, Set.mem_iUnion.2 ⟨Quot.mk (Isom I.E I.n) (latOf I h z), Set.mem_univ _, ?_⟩⟩
    show (pt (Quot.mk (Isom I.E I.n) (latOf I h z))).2⁻¹ * (a * z).2 ∈ I.Kset
    rw [hpt]
    exact hk
  calc covol I.GFset (I.muA μf) Set.univ ≤ I.muA μf (⋃ q, D q) := by
        unfold covol
        exact iInf_le_of_le _ (iInf_le_of_le (MeasurableSet.iUnion hDm) (iInf_le_of_le hcover le_rfl))
    _ ≤ ∑ q, I.muA μf (D q) := measure_iUnion_fintype_le _ _
    _ = ∑ _q : Quot (Isom I.E I.n), (∏ v, Formalism.REAL.muG (I.ε v) Set.univ) * μf I.Kset := by
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [D, AutInst.muA]
        rw [Measure.prod_prod, Measure.pi_univ, measure_preimage_mul]
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

theorem volU_pos (i : ℕ) : 0 < volU i := by
  unfold volU sphV
  exact mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

theorem gauge_local (N : ℕ) (ε : Fin N → Bool) (hε : ε = allPos N) (c : ℝ) (hc : IsGauge ε c) :
    0 ≤ c ∧ ENNReal.ofReal c * Formalism.REAL.muG ε Set.univ = ENNReal.ofReal (volU N) := by
  subst hε
  have h1 := GlobalTheory.T.riemannianHaarGauge_volume_unitaryGroup_eq N c hc
  have hlt := GlobalTheory.UnitaryVolume.muG_univ_lt_top N
  have hne := GlobalTheory.UnitaryVolume.muG_univ_ne_zero N
  have ht : 0 < (Formalism.REAL.muG (allPos N) Set.univ).toReal := ENNReal.toReal_pos hne hlt.ne
  have hc0 : 0 < c := by
    by_contra hle
    push_neg at hle
    nlinarith [volU_pos N]
  refine ⟨hc0.le, ?_⟩
  rw [← ENNReal.ofReal_toReal hlt.ne, ← ENNReal.ofReal_mul hc0.le, h1]

theorem gaugeVol_le : ∀ (I : AutInst) (r : ℕ), HasSig I r 0 → ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure], IsGaugeAll I c → gaugeVol I c μf ≤ ENNReal.ofReal (volU r ^ I.f) * ((defClassNum I.E r : ENat) : ENNReal) := by
  intro I r h c μf _ _ hc
  obtain rfl := rank_eq I h
  have hK := GlobalTheory.adelicStab_isCompact_isOpen I
  have h1K : (1 : I.Gf) ∈ I.Kset :=
    (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I 1 1).2 (by rw [mul_one])
  have hKpos : μf I.Kset ≠ 0 := (hK.2.1.measure_pos μf ⟨1, h1K⟩).ne'
  have hKtop : μf I.Kset ≠ ⊤ := hK.1.measure_lt_top.ne
  have hloc : ∀ v, 0 ≤ c v ∧
      ENNReal.ofReal (c v) * Formalism.REAL.muG (I.ε v) Set.univ = ENNReal.ofReal (volU I.n) :=
    fun v => gauge_local I.n (I.ε v) (eps_eq I h v) (c v) (hc v)
  have hV : ENNReal.ofReal (volU I.n ^ I.f) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (pow_pos (volU_pos _) _)).ne'
  have hprod : ENNReal.ofReal (∏ v, c v) * ∏ v, Formalism.REAL.muG (I.ε v) Set.univ =
      ENNReal.ofReal (volU I.n ^ I.f) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun v _ => (hloc v).1), ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl (fun v _ => (hloc v).2), Finset.prod_const, Finset.card_univ, card_places,
      ENNReal.ofReal_pow (volU_pos _).le]
  by_cases hfin : Finite (Quot (Isom I.E I.n))
  · haveI := Fintype.ofFinite (Quot (Isom I.E I.n))
    have hcv := covol_le I h μf
    unfold gaugeVol
    calc ENNReal.ofReal (∏ v, c v) * covol I.GFset (I.muA μf) Set.univ / μf I.Kset
        ≤ ENNReal.ofReal (∏ v, c v) * ((∏ v, Formalism.REAL.muG (I.ε v) Set.univ) *
            ((Fintype.card (Quot (Isom I.E I.n)) : ENNReal) * μf I.Kset)) / μf I.Kset := by
          gcongr
      _ = ENNReal.ofReal (volU I.n ^ I.f) * (Fintype.card (Quot (Isom I.E I.n)) : ENNReal) := by
          rw [← mul_assoc, hprod, ← mul_assoc, ENNReal.mul_div_cancel_right hKpos hKtop]
      _ = ENNReal.ofReal (volU I.n ^ I.f) * ((defClassNum I.E I.n : ENat) : ENNReal) := by
          rw [defClassNum, ENat.card_eq_coe_fintype_card, ENat.toENNReal_coe]
  · haveI := not_finite_iff_infinite.1 hfin
    rw [defClassNum, ENat.card_eq_top_of_infinite, ENat.toENNReal_top, ENNReal.mul_top hV]
    exact le_top

end GlobalTheory.DefiniteVolume
end
end

