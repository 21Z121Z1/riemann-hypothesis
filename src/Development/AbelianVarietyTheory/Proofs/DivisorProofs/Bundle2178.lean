import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2157
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2120
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2158
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMulAndFaithfulFiniteGroup
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

set_option autoImplicit false
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise

namespace GlobalTheory.LevelFaithful

theorem bc_eq_one_of_cong {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) (H : Set (Fin n → R)) (N : ℕ)
    (hH : ∀ z, z ∈ H ↔ ∀ i, ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).mulVec z i ∈ S)
    (y : GL (Fin n) S) (s : S)
    (hx : ∀ z ∈ H, ∃ w ∈ H, (s : R) • ((β * Formalism.UG.bc S.subtype y * β⁻¹ : GL (Fin n) R).1 *ᵥ z - z) = N • w)
    {k : Type} [CommRing k] (φ : S →+* k) (hN : (N : k) = 0) (hs : IsUnit (φ s)) : Formalism.UG.bc φ y = 1 := by
  have key : ∀ i j, φ (y.1 i j) = (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    have e0 : (β⁻¹).1 *ᵥ (β.1 *ᵥ Pi.single j 1) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    obtain ⟨w, hw, e⟩ := hx (β.1 *ᵥ Pi.single j 1) ((hH _).2 fun i => by
      rw [e0, Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _])
    have e1 := congrArg (fun v => ((β⁻¹).1 *ᵥ v) i) e
    have hy : (Formalism.UG.bc S.subtype y).1 i j = (y.1 i j : R) := rfl
    simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, e0, Units.val_mul, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul] at e1
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Matrix.mulVec_single_one] at e1
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Matrix.col_apply, hy] at e1
    have hc := (hH w).1 hw i
    have e2 : s * (y.1 i j - (Pi.single j 1 : Fin n → S) i) = N • (⟨_, hc⟩ : S) := by
      apply Subtype.ext
      change (s : R) * ((y.1 i j : R) - ((Pi.single j (1 : S) : Fin n → S) i : R)) =
        N • (((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ w) i
      rw [← e1]
      congr 2
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    have e3 := congrArg φ e2
    rw [map_mul, map_nsmul, nsmul_eq_mul, hN, zero_mul, hs.mul_right_eq_zero, map_sub, sub_eq_zero] at e3
    rw [e3, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact key i j

theorem cong_swap_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (t : FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    (K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
      t • (K *ᵥ z - z) = N • y) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∃ y ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      Algebra.TensorProduct.comm F _ E t • (K.map (Algebra.TensorProduct.comm F _ E) *ᵥ z - z) = N • y := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h _ (GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ z hz)
  refine ⟨_, GlobalTheory.PrincInLevel.swap_mem_hatL Λ y hy, funext fun i => ?_⟩
  have := congrArg (Algebra.TensorProduct.comm F _ E) (congrFun e i)
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, map_nsmul, Matrix.mulVec, dotProduct, map_sum,
    AlgEquiv.apply_symm_apply, Matrix.map_apply] using this

end GlobalTheory.LevelFaithful

namespace GlobalTheory.LevelFaithful

variable {D : D7}

theorem smul_mem_latGHat {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (c : 𝓞 D.host.E) {w : Fin V.rank → FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E}
    (hw : w ∈ latGHat V 1) :
    ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E)) • w ∈ latGHat V 1 := by
  have hl' : latHat V = GlobalTheory.AdLat.hat D.host.F ((Λ : Submodule (𝓞 D.host.E) _) : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.OneMapRef.Lift.hatV_eq hβ).symm
  set s : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
    (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E) with hs
  have e : ∀ z : Fin V.rank → FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E,
      Matrix.diagonal (fun _ => s) *ᵥ z = s • z := fun z => by
    funext j; rw [Matrix.mulVec_diagonal]; rfl
  have hN : ∀ z ∈ latHat V, Matrix.diagonal (fun _ => s) *ᵥ z ∈ latHat V := by
    intro z hz
    rw [e]
    rw [hl'] at hz ⊢
    have := GlobalTheory.PrincInLevel.smul_mem_hat Λ _ (Formalism.L2.DIV.oToS D.host.F D.host.E c).2 z hz
    convert this using 2
    rw [Formalism.L2.DIV.oToS_coe, Algebra.TensorProduct.comm_symm_tmul]
  rw [← e]
  exact GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN w hw

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem cong_of_trivial {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} {Mb Mh : Ideal (𝓞 D.host.E)}
    (hprod : Mb * Mh = Ideal.span {(M : 𝓞 D.host.E)}) {c : 𝓞 D.host.E} (hc : c ∈ Mh) {f : La →ₗ[𝓞 D.host.E] La}
    (hd : ∀ a, f a - a ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La))
    (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))
    (hcong : ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - K *ᵥ finVec V (ι a) = M • w) (a : La) :
    ∃ w ∈ latGHat V 1,
      (((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E)) *
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E))) •
        (K *ᵥ finVec V (ι a) - finVec V (ι a)) = M • w := by
  set s : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
    (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E) with hs
  obtain ⟨w, hw, e⟩ := hcong (c • a) (Submodule.smul_mem_smul hc Submodule.mem_top)
  have hdm : c • (f (c • a) - c • a) ∈ (M : 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) La) := by
    have := Submodule.smul_mem_smul hc (hd (c • a))
    rw [← Submodule.mul_smul, mul_comm, hprod, Submodule.ideal_span_singleton_smul] at this
    exact this
  obtain ⟨m, -, hm'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hdm
  set F := GlobalTheory.LevelActionPinned.fvec V ι with hF
  have eF : ∀ (b : 𝓞 D.host.E) x, F (b • x) =
      ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • F x :=
    fun b x => GlobalTheory.LevelActionPinned.fvec_smul V ι b x
  have E1 : F (c • a) = s • F a := eF c a
  have eM : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (((M : ℕ) : 𝓞 D.host.E) : D.host.E)) =
      ((M : ℕ) : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := by
    have h0 : (((M : ℕ) : 𝓞 D.host.E) : D.host.E) = ((M : ℕ) : D.host.E) := by simp
    rw [h0]
    exact map_natCast (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] _) _
  have E2 : s • (F (f (c • a)) - F (c • a)) = M • F m := by
    rw [← map_sub, ← eF, ← hm', eF, eM, Nat.cast_smul_eq_nsmul]
  have e' : F (f (c • a)) - K *ᵥ F (c • a) = M • w := e
  refine ⟨F m - s • w, sub_mem (((GlobalTheory.MarkCoset.latG_spec D V 1).1 _).1
    (hι.2 ▸ LinearMap.mem_range_self ι m)) (smul_mem_latGHat hβ c hw), ?_⟩
  show (s * s) • (K *ᵥ F a - F a) = _
  calc (s * s) • (K *ᵥ F a - F a) = s • (K *ᵥ (s • F a) - s • F a) := by
        rw [mul_smul, Matrix.mulVec_smul K s (F a), smul_sub]
    _ = s • ((F (f (c • a)) - F (c • a)) - M • w) := by
        rw [← E1, ← e']; congr 1; abel
    _ = M • (F m - s • w) := by
        rw [smul_sub, E2, smul_comm s M w, smul_sub]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rTup_eq_one_of_cong {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {M : ℕ} {c : 𝓞 D.host.E}
    (hM : ∀ PP ∈ L.Pg, ((M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (hc : ∀ PP ∈ L.Pg, c - 1 ∈ PP.asIdeal) {κ : GA D V}
    (hκ : Lev.finE V κ ∈ Formalism.L2.DIV.St β)
    (h : ∀ z ∈ latHat V, ∃ y ∈ latHat V,
      (((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E)) *
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E))) •
        ((finHom V κ).1 *ᵥ z - z) = M • y) :
    Formalism.L2.DIV.rTup β L (Lev.finE V κ) = 1 := by
  have hl' : latHat V = GlobalTheory.AdLat.hat D.host.F ((Λ : Submodule (𝓞 D.host.E) _) : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.OneMapRef.Lift.hatV_eq hβ).symm
  rw [hl'] at h
  have hS := cong_swap_smul Λ M _ _ h
  obtain ⟨yi, hyi⟩ := hκ
  obtain ⟨cc, hfr, -⟩ := hβ
  have hx : ∀ z ∈ (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)), ∃ w ∈
      (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)),
      ((Formalism.L2.DIV.oToS D.host.F D.host.E (c * c) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) •
        ((β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype yi * β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 *ᵥ z - z) =
        M • w := by
    intro z hz
    obtain ⟨y, hy, e⟩ := hS z hz
    refine ⟨y, hy, ?_⟩
    have hs' : ((Formalism.L2.DIV.oToS D.host.F D.host.E (c * c) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
        Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E
          (((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E)) *
            ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E))) := by
      rw [Formalism.L2.DIV.oToS_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.comm_tmul, map_mul]
    have e2 : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype yi * β⁻¹ = Formalism.L2.DIV.frGL β yi := rfl
    have hK' : (β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype yi * β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 =
        (finHom V κ).1.map (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E) := by
      rw [e2, hyi]
      rfl
    rw [hs', hK']
    exact e
  have hred : ∀ PP ∈ L.Pg, Formalism.L2.DIV.redFn β PP (Lev.finE V κ) = 1 := by
    intro PP hP
    have hN : ((M : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (hM PP hP)
    have hsu : IsUnit (Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E (c * c))) := by
      rw [Formalism.L2.DIV.resS_oToS]
      have e1 : Ideal.Quotient.mk PP.asIdeal c = 1 := by
        rw [← map_one (Ideal.Quotient.mk PP.asIdeal)]
        exact Ideal.Quotient.eq.2 (hc PP hP)
      rw [map_mul, e1, mul_one]
      exact isUnit_one
    have hr := bc_eq_one_of_cong (Formalism.L2.Herm.intAf D.host.F D.host.E) β
      (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)) M hfr yi
      (Formalism.L2.DIV.oToS D.host.F D.host.E (c * c)) hx (Formalism.L2.DIV.resS D.host.F PP) hN hsu
    rw [← hyi, Formalism.L2.DIV.redFn_frGL, hr]
  have e3 : Formalism.L2.DIV.rTup β L (Lev.finE V κ) = Formalism.L2.DIV.rTup β L 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ _ = Formalism.L2.DIV.upperLeftBlock _ _
    rw [hred PP.1 PP.2, Formalism.L2.DIV.redFn_one]
  rw [e3, Formalism.L2.DIV.rTup_one]

end GlobalTheory.LevelFaithful

open GlobalTheory.LevelFaithful in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.LevelFaithful.lev_mul_and_faithful : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m), (∀ g g' : p.P.Gp, r.lev i (g * g') = r.lev i g * r.lev i g') ∧ ∀ g : p.P.Gp, r.lev i g = 1 → g = 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i
  obtain ⟨v⟩ := GlobalTheory.ShareOn.nonempty_place D
  have hlev := h.level v i
  have hι := GlobalTheory.TraceLattice.latEmb_iotaW (h.laws v) i
  have hβ : IsSDFrame (Wc D i) ((R2 p).βW i) ((R2 p).ΛW i) 1 := p.charW.base.lev.βW i
  obtain ⟨h1, hm⟩ := GlobalTheory.LevelActionPinned.congr_of_levIs (R2 p) i hι hβ h.half hlev
  refine ⟨fun g g' => ?_, fun g hg => ?_⟩
  · refine LinearEquiv.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e1 := liftLa_spec (r.lev i (g * g')) a
    have e2 := liftLa_spec (r.lev i g) (liftLa (r.lev i g') a)
    have e3 := liftLa_spec (r.lev i g') a
    simp only [Submodule.mkQ_apply] at e1 e2 e3
    rw [LinearEquiv.mul_apply, ← e3, ← e2, ← e1]
    exact (Submodule.Quotient.eq _).2 (hm g g' a)
  · apply (R2 p).eG.injective
    rw [map_one]
    obtain ⟨κ, hκ, hcong⟩ := hlev g
    rw [← hκ.2.2]
    have hd : ∀ a, liftLa (r.lev i g) a - a ∈
        p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
      intro a
      rw [hg, ← Submodule.Quotient.eq]
      exact liftLa_spec 1 a
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.1
      (p.T.Q.l.coprime ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ p.T.Q.l.Mb ⊔ Mfr p.T.Q.l)
    have hc1 : c - 1 ∈ p.T.Q.l.Mb := by
      have e : c - 1 = -b := by rw [← hbc]; ring
      rw [e]; exact neg_mem hb
    have hMbP : ∀ PP ∈ (R2 p).Pg, p.T.Q.l.Mb ≤ PP.asIdeal := fun PP hP => by
      rw [h.half]; exact Ideal.prod_le_inf.trans (Finset.inf_le hP)
    have hp : p.T.Q.l.Mb * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := p.T.Q.l.prod
    have hMm : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb := by
      have h0 : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb * Mfr p.T.Q.l := by
        rw [hp]; exact Ideal.mem_span_singleton_self _
      exact (Ideal.mul_le_inf.trans (inf_le_left : p.T.Q.l.Mb ⊓ Mfr p.T.Q.l ≤ p.T.Q.l.Mb)) h0
    have hA := cong_of_trivial hβ hι hp hc hd _ hcong
    have hB := GlobalTheory.T.congruence_on_selfDual_lattice_completion (Wc D i) hβ _ _ _ (GlobalTheory.T.congruence_on_selfDual_lattice_of_datum_image (Wc D i) hβ hι _ _ _ hA)
    exact rTup_eq_one_of_cong hβ ((R2 p).datWp i (R2 p).triv) (fun PP hP => hMbP PP hP hMm)
      (fun PP hP => hMbP PP hP hc1) (Formalism.L2.DIV.parLev_St hκ.2.1) hB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftDatumConjugateHalfFiniteFourierSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LiftFour

theorem dil_add {D : D7} (i : Fin D.R.m) (a : D.host.E) (x y : WO (Vc D i) (Wc D i)) :
    dil i a (x + y) = dil i a x + dil i a y := by
  exact Matrix.ext fun p q => by simp only [dil, Matrix.map_apply, Matrix.add_apply, mul_add]

theorem isHalf_add {D : D7} {m n : ℕ} {e : AE D} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) :
    IsHalf e (x + y) := fun p q => by simp only [Matrix.add_apply, mul_add, hx p q, hy p q]

theorem isHalf_of_add {D : D7} {m n : ℕ} {e : AE D} {x y : Mx D m n} (hxy : IsHalf e (x + y)) (hy : IsHalf e y) :
    IsHalf e x := fun p q => by
  have h1 := hxy p q
  simp only [Matrix.add_apply, mul_add, hy p q] at h1
  exact add_right_cancel h1

theorem isHalf_dil {D : D7} (i : Fin D.R.m) {e : AE D} {a : D.host.E} (ha : a ≠ 0) (x : WO (Vc D i) (Wc D i)) :
    IsHalf e (dil i a x) ↔ IsHalf e x := by
  have hu : incA D a⁻¹ * incA D a = 1 := by rw [← RingHom.map_mul, inv_mul_cancel₀ ha, map_one]
  constructor
  · intro h p q
    have h1 : e * (incA D a * x p q) = incA D a * x p q := h p q
    linear_combination (incA D a⁻¹) * h1 - (e * x p q - x p q) * hu
  · intro h p q
    show e * (incA D a * x p q) = incA D a * x p q
    rw [mul_left_comm, h p q]

theorem redM_frMapO_add {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (PP : Pl D.host.E) (a b : WO S T) (ha : IsIntM (frMapO S T βS βT a)) (hb : IsIntM (frMapO S T βS βT b)) :
    redM PP (frMapO S T βS βT (a + b)) = redM PP (frMapO S T βS βT a) + redM PP (frMapO S T βS βT b) := by
  have e : frMapO S T βS βT (a + b) = frMapO S T βS βT a + frMapO S T βS βT b := by
    ext p q
    have := GlobalTheory.PlaceDatum.frMapO_add βS βT a b 1 p q
    simpa using this
  ext p q
  simp only [redM, e, Matrix.add_apply, Matrix.of_apply]
  rw [dif_pos (add_mem (ha p q) (hb p q)), dif_pos (ha p q), dif_pos (hb p q), ← map_add]
  rfl

theorem datum_conj_half_fourier : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → (∀ PP ∈ Q, ξR PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∃ (Y : Finset (WO (Vc D i) (Wc D i))) (a : WO (Vc D i) (Wc D i) → ℂ) (Gc : ℂ), UnitOff N Gc ∧ (∀ y ∈ Y, IsHalf eQ y) ∧
      (∀ t, (if IsHalf (cA D eQ) t ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t) then
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t)) else 0) =
        halfInd (cA D eQ) (lattice₂ R i) t * ∑ y ∈ Y, a y * R.ψ (symplO (Vc D i) (Wc D i) t y)) ∧
      ∀ t, ∑ y ∈ Y, a y * halfInd eQ (lattice₂ R i) (t + y) = Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i hV ξR Q hQ hξ N hN hNQ eQ heQ ϖ hϖ hϖQ
  classical
  letI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => Fintype.ofFinite _
  have hϖ' : (ϖ : D.host.E) ≠ 0 := by
    intro h; exact hϖ (by exact_mod_cast h)
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hrn : (Wc D i).rank ≤ (Vc D i).rank := by rw [rV, rW]; omega
  obtain ⟨ψP, hψP, hchar⟩ := GlobalTheory.T.exists_uniformizer_section_at_prime_set D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ ϖ hϖ hϖQ
  obtain ⟨c, hinv, hc⟩ := GlobalTheory.T.residueMatrixDatum_fourierExpansion_gaussSum D Q (Vc D i).rank (Wc D i).rank hrn ψP ξR hψP hξ
  choose yx hyh hyl hyr using GlobalTheory.T.exists_half_dilated_reduction_residueMatrices D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ ϖ hϖ hϖQ
  have hker := GlobalTheory.T.mem_lattice_iff_uniformiser_reduction_vanishes D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ ϖ hϖ hϖQ
  have h4a := GlobalTheory.T.mem_completedPairLattice_iff_adjointFrameMatrix_integral_conjHalf D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ
  have h4b := GlobalTheory.T.mem_completedPairLattice_iff_frameMatrix_integral_on_half D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ
  have hdm := GlobalTheory.T.completedPairLattice_dilation_mem_of_integer D G Pl0 T0 A Ks R i ϖ
  have key : ∀ g : WO (Vc D i) (Wc D i) → ℂ,
      ∑ y ∈ Finset.univ.image yx, (∑ x ∈ Finset.univ.filter (fun x => yx x = y), c x) * g y = ∑ x, c x * g (yx x) := by
    intro g
    simp_rw [Finset.sum_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image yx) (g := yx)
      (fun x _ => Finset.mem_image_of_mem yx (Finset.mem_univ x))]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]
  refine ⟨Finset.univ.image yx, fun y => ∑ x ∈ Finset.univ.filter (fun x => yx x = y), c x, _,
    GlobalTheory.T.isUnitAwayFromLevel_prod_normalised_matrixGaussSum D Q (Vc D i).rank (Wc D i).rank hrn ψP ξR hψP hξ N hN hNQ, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
    exact hyh x
  · intro t
    rw [key (fun y => R.ψ (symplO (Vc D i) (Wc D i) t y))]
    by_cases ht : IsHalf (cA D eQ) t
    · by_cases hl : t ∈ lattice₂ R i
      · have hint := (h4a t ht).2 hl
        rw [if_pos ⟨ht, hint⟩, halfInd, if_pos ⟨hl, ht⟩, one_mul, hinv]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hchar t (yx x) ht hl (hyh x) (hyl x), ← Finset.prod_attach Q]
        refine congrArg _ (Finset.prod_congr rfl fun PP _ => ?_)
        rw [hyr x PP]
      · rw [if_neg (fun h => hl ((h4a t ht).1 h.2)), halfInd, if_neg (fun h => hl h.1), zero_mul]
    · rw [if_neg (fun h => ht h.1), halfInd, if_neg (fun h => ht h.2), zero_mul]
  · intro t
    rw [key (fun y => halfInd eQ (lattice₂ R i) (t + y)), flatDat]
    by_cases ht : IsHalf eQ t
    · have hdt : IsHalf eQ (dil i (ϖ : D.host.E) t) := (isHalf_dil i hϖ' t).2 ht
      by_cases hl : dil i (ϖ : D.host.E) t ∈ lattice₂ R i
      · have hint := (h4b _ hdt).2 hl
        rw [if_pos ⟨hdt, hint⟩]
        set ρt : ∀ PP : ↥Q, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP.1) :=
          fun PP => redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) t)) with hρt
        have hterm : ∀ x, halfInd eQ (lattice₂ R i) (t + yx x) = if x = -ρt then 1 else 0 := by
          intro x
          have hh : IsHalf eQ (t + yx x) := isHalf_add ht (hyh x)
          have hdl : dil i (ϖ : D.host.E) (t + yx x) ∈ lattice₂ R i := by
            rw [dil_add]; exact add_mem hl (hyl x)
          have hintx := (h4b _ ((isHalf_dil i hϖ' _).2 (hyh x))).2 (hyl x)
          rw [halfInd]
          by_cases hx : x = -ρt
          · have hm : t + yx x ∈ lattice₂ R i := by
              refine (hker _ hh hdl).2 fun PP hPP => ?_
              rw [dil_add, redM_frMapO_add _ _ _ _ _ hint hintx, hyr x ⟨PP, hPP⟩, hx]
              simp [hρt]
            rw [if_pos hx, if_pos ⟨hm, hh⟩]
          · rw [if_neg hx, if_neg]
            rintro ⟨hm, -⟩
            apply hx
            funext PP
            have h0 := (hker _ hh hdl).1 hm PP.1 PP.2
            rw [dil_add, redM_frMapO_add _ _ _ _ _ hint hintx, hyr x PP] at h0
            rw [Pi.neg_apply, hρt]
            exact eq_neg_of_add_eq_zero_right h0
        simp_rw [hterm, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ (-ρt) c, if_pos (Finset.mem_univ _)]
        exact hc ρt _ fun PP => rfl
      · rw [if_neg (fun h => hl ((h4b _ hdt).1 h.2))]
        rw [mul_zero]
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [halfInd, if_neg, mul_zero]
        rintro ⟨hm, -⟩
        apply hl
        have := hdm _ hm
        rw [dil_add] at this
        simpa using sub_mem this (hyl x)
    · rw [if_neg (fun h => ht ((isHalf_dil i hϖ' t).1 h.1))]
      rw [mul_zero]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [halfInd, if_neg, mul_zero]
      rintro ⟨-, hh⟩
      exact ht (isHalf_of_add hh (hyh x))

end GlobalTheory.LiftFour
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoTangentPullConstantDeformation
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TangentConstLB

theorem symIso_of_comm {S₀ S₁ : Scheme.{0}} {X : Over S₀} {A' : Over S₁} [GrpObj X] [GrpObj A']
    {L : LB X.left} (hL : L.IsLB)
    (hS : LBIso L (L.pull (GrpObj.inv : X ⟶ X).left)) (f : A'.left ⟶ X.left)
    (hf : (GrpObj.inv : A' ⟶ A').left ≫ f = f ≫ (GrpObj.inv : X ⟶ X).left) :
    LBIso ((L.pull f).pull (GrpObj.inv : A' ⟶ A').left) (L.pull f) := by
  have h1 := GlobalTheory.FamRep.lbIso_pull_pull hL f (GrpObj.inv : A' ⟶ A').left
  rw [hf] at h1
  have h2 := (GlobalTheory.FamRep.lbIso_pull_pull hL (GrpObj.inv : X ⟶ X).left f).symm
  have h3 := GlobalTheory.FamRep.lbIso_pull hS.symm f
  have hinv := pull_isLB hL (GrpObj.inv : X ⟶ X).left
  exact LBIso.trans (pull_isLB (pull_isLB hL f) _) (pull_isLB hL _) (pull_isLB hL f) h1
    (LBIso.trans (pull_isLB hL _) (pull_isLB hinv f) (pull_isLB hL f) h2 h3)

theorem lbIso_tangent_const :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x₀ : Sp K ⟶ Xo.X) (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G x₀ π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) := by
  intro E _ _ _ H Dw l Xo c K _ _ x₀ x' A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hAbG : IsAbelianScheme Xo.univ.t.G := by
    haveI := Xo.univ.proper
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ Xo.univ.t.semi
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAbG hπ
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨-, w, hw, -⟩ := Xo.univ.t.sym
  have hS : LBIso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left) := ⟨w, hw⟩
  have c1 : (GrpObj.inv : A' ⟶ A').left ≫ π' = π' ≫ (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left :=
    GlobalTheory.PolBaseChange.inv_comm hπ'
  have c2 : (GrpObj.inv : A' ⟶ A').left ≫ (q ≫ π) = (q ≫ π) ≫ (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left := by
    rw [← Category.assoc, GlobalTheory.PolBaseChange.inv_comm hq, Category.assoc, GlobalTheory.PolBaseChange.inv_comm hπ,
      Category.assoc]
  have f1 := GlobalTheory.FamRep.lbIso_pull_pull hL π' i
  rw [hiπ] at f1
  have f2 := GlobalTheory.FamRep.lbIso_pull_pull hL (q ≫ π) i
  rw [← Category.assoc, hiq, Category.id_comp] at f2
  exact GlobalTheory.SymFirstOrder.lbIso_of_symmetric K A A' i q hA hi hq hiq _ _ (pull_isLB hL π') (pull_isLB hL (q ≫ π))
    (symIso_of_comm hL hS π' c1) (symIso_of_comm hL hS (q ≫ π) c2)
    (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) f1 f2.symm)

end GlobalTheory.TangentConstLB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqIntegralMatrixIndicatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModel_vacuum_eq_integralMatrix_indicator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X → ∀ w ∈ locPl G t, ∀ ι : ToA G t i j w, IsMixModelA W B t e Γ w ι →
      ι (Γ.M.vac _) = ι (Γ.M.vac _) 0 • Set.indicator {Z | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer} 1 := by
  first | exact @GlobalTheory.MixVacBig.mix_vac | exact GlobalTheory.MixVacBig.mix_vac | (intros; apply GlobalTheory.MixVacBig.mix_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinitionStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliLaws_of_principalLevel_fieldOfDefinition : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, Formalism.L2.Theta.GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → FnAlgClosed Xo c → (∀ p : ℕ, p.Prime → l.GoodAt p) → Laws U (xiR D) ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H := by
  first | exact @GlobalTheory.LevLaws.laws_of_level | exact GlobalTheory.LevLaws.laws_of_level | (intros; apply GlobalTheory.LevLaws.laws_of_level <;> assumption)
end

