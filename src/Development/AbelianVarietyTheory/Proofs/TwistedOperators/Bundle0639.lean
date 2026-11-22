import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0452
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0223
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0188
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0454
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0327
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0380
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0258
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0482
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0334
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0452
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0634
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0183
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0629
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0617

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthCongruenceSubgroupCompactOpenPlacesToAdeles
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PlaceLevelCosets

variable {D : D7}

theorem mem_GinfC_of_off (V : HSp D) (S : GlobalTheory.FinPl.Pl D → Prop) {g : GA D V} (h1 : g ∈ grpOff V S)
    (h2 : g ∈ grpOff V (fun v => ¬ S v)) : g ∈ GinfC V := by
  have h3 : g ∈ grpOff V (fun _ => True) := by
    refine GlobalTheory.FinPl.PlacesAdeles.mem_congGrp.2 fun i j => ?_
    have a := GlobalTheory.FinPl.PlacesAdeles.mem_congGrp.1 h1 i j
    have b := GlobalTheory.FinPl.PlacesAdeles.mem_congGrp.1 h2 i j
    simp only [GlobalTheory.FinPl.idOff, Submodule.mem_iInf] at a b ⊢
    intro w
    by_cases hw : S w.1
    · exact a ⟨w.1, hw⟩
    · exact b ⟨w.1, hw⟩
  exact GlobalTheory.FinPl.OffInh.mem_GinfC_of_all (fun _ => trivial) h3

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem mem_lev_of_inK {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (X : Node)
    (hΛ : Submodule.IsLattice D.host.E (G.Λ X)) {κ : GA D (G.V X)}
    (hκ : InK (G.V X) (G.Λ X) (fun v => v ∉ G.pl.S0) κ) : κ ∈ lev G X := by
  classical
  have hfg : (G.Λ X).FG := Submodule.IsLattice.fg (A := D.host.E)
  obtain ⟨hGf, hpr⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff (G.V X) _ κ).1 hκ.1
  obtain ⟨β, hβ⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E (G.V X).rank (G.Λ X) hΛ
  have hS : Lev.finE (G.V X) κ ∈ Formalism.L2.DIV.St β :=
    (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (G.V X) β (G.Λ X) hβ κ).2
      (GlobalTheory.AdelicU.mem_levelOpen.1 (GlobalTheory.FinPl.KOpen.levelOpen_of_inK (G.V X) (G.Λ X) hfg _ hκ))
  refine ⟨hGf, ?_⟩
  show Lev.finE (G.V X) κ ∈ congLev D.sp.cm (G.V X).gram (G.Λ X) G.modul
  rw [← GlobalTheory.ColMeas.princ_eq_congLev D.sp.cm (G.V X).gram hβ G.modul]
  refine ⟨GlobalTheory.LevSplit.finE_mem_UA (G.V X) κ, ?_⟩
  obtain ⟨y, hy⟩ := hS
  refine GlobalTheory.Grid.mem_princGL.2 ⟨y, hy, fun a b => ?_⟩

  have hE : ∀ c d, ((Lev.finE (G.V X) κ).1 - 1) c d = toEAf D ((Formalism.L2.Theta.mt (G.V X) κ - 1) c d) := by
    intro c d
    rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
    congr 1
    by_cases h : c = d
    · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, RingHom.map_zero]
  have hW : ∀ w ∈ G.pl.W0, ((Lev.finE (G.V X) κ).1 - 1).map (GlobalTheory.StdFrames.cpt w) = 0 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    have h1 := (GlobalTheory.FinPl.KOpen.proj_eq_one_iff (G.V X) v κ).1 (hpr v (not_not.2 hv))
    refine Matrix.ext fun c d => ?_
    rw [Matrix.map_apply, hE, Matrix.zero_apply]
    exact (GlobalTheory.LocHat.prV_eq_zero_iff_cpt v _).1 (GlobalTheory.StabOff.prV_toEAf_eq_zero v _ (h1 c d)) _ (G.pl.under_w hv)
  have hconj : (Lev.finE (G.V X) κ).1 = β.1 * (Formalism.L2.DIV.intGL D.host.F D.host.E _ y).1 * (β⁻¹).1 := by
    rw [← hy]; rfl
  have hY := GlobalTheory.LevRedTriv.conj_sub_one β _ _ hconj
  refine (GlobalTheory.FunObj.Comparison₂.mem_idS_modul G _).2 fun w hw => ?_
  have hM : ((Formalism.L2.DIV.intGL D.host.F D.host.E _ y).1 - 1).map (GlobalTheory.StdFrames.cpt w) = 0 := by
    rw [hY, Matrix.map_mul, Matrix.map_mul, hW w hw, Matrix.mul_zero, Matrix.zero_mul]
  have e0 : GlobalTheory.StdFrames.cpt w (((y.1 - 1) a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = 0 := by
    rw [GlobalTheory.LevRedTriv.coe_sub_one_apply]
    exact congrFun (congrFun hM a) b
  rw [e0, map_zero]
  exact zero_le'

theorem idAt_le_idOff_compl (P : GlobalTheory.FinPl.Pl D → Prop) : idAt D (fun v => ¬ P v) ≤ idOff D P := by
  intro a ha
  simp only [GlobalTheory.FinPl.idAt, GlobalTheory.FinPl.idOff, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact fun w => ha.2 ⟨w.1, not_not.2 w.2⟩

theorem idAt_le_idOff_compl' (P : GlobalTheory.FinPl.Pl D → Prop) : idAt D P ≤ idOff D (fun v => ¬ P v) := by
  intro a ha
  simp only [GlobalTheory.FinPl.idAt, GlobalTheory.FinPl.idOff, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact fun w => ha.2 ⟨w.1, w.2⟩

end GlobalTheory.PlaceLevelCosets

open GlobalTheory.PlaceLevelCosets GlobalTheory.FinPl.PlacesAdeles in

theorem GlobalTheory.PlaceLevelCosets.levCoset_of_places : All fun {D} _ _ _ {G} _ _ => ∀ i, i ≤ D.R.m → (lev G (.grid i 0) ≤ GfC _ ∧ IsCompact (lev G (.grid i 0) : Set (GA D (G.V (.grid i 0)))) ∧ IsOpen (((lev G (.grid i 0)).subgroupOf (GfC _) : Subgroup (GfC (G.V (.grid i 0)))) : Set (GfC (G.V (.grid i 0))))) ∧ ∀ (R : Subgroup (GA D (G.V (.grid i 0)))) h, (∀ v ∉ G.pl.S0, ∀ h₁ ∈ grpAt _ (· = v), ∀ h₂ ∈ grpOff _ (· = v), h = h₁ * h₂ → CosetAt _ R (G.Λ (.grid i 0)) v h₁) → (∀ h₁ ∈ grpAt _ (fun v => v ∈ G.pl.S0), ∀ h₂ ∈ grpOff _ (fun v => v ∈ G.pl.S0), h = h₁ * h₂ → ∃ r ∈ R, r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid i 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ h₁ = r * k) → ∃ r ∈ R, ∃ a ∈ GinfC _, ∃ k ∈ lev G (.grid i 0), h = r * a * k := by
  intro D _ T L μ0 hL sc G W M _ i hi
  have hV := node_isV G hL (X := .grid i 0) ⟨hi, Nat.zero_le _⟩
  have hlat : Submodule.IsLattice D.host.E (G.Λ (.grid i 0)) := hV.sd.1
  have hoc := congLev_open_compact (G.V (.grid i 0)) hlat (G.pl.modul_ne_bot sc)
  refine ⟨⟨inf_le_left, hoc.2, ?_⟩, ?_⟩
  · have e : (((lev G (.grid i 0)).subgroupOf (GfC _) : Subgroup (GfC (G.V (.grid i 0)))) : Set (GfC (G.V (.grid i 0)))) =
        Subtype.val ⁻¹' ((((congLev D.sp.cm (G.V (.grid i 0)).gram (G.Λ (.grid i 0)) G.modul).comap
          (Lev.finE (G.V (.grid i 0))) : Subgroup (GA D (G.V (.grid i 0)))) : Set (GA D (G.V (.grid i 0))))) := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [e]
    exact hoc.1.preimage continuous_subtype_val
  · intro R h hA hB
    have hsd : IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := hV.sd
    have hoff : ∀ v, (fun v => v ∉ G.pl.S0) v → ∃ hv ∈ grpAt (G.V (.grid i 0)) (· = v), ∃ h' ∈ grpOff (G.V (.grid i 0)) (· = v),
        h = hv * h' ∧ ∃ r ∈ R, r ∈ grpAt (G.V (.grid i 0)) (· = v) ∧ ∃ κ, InK (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) κ ∧
          hv = r * κ := by
      intro v hv
      obtain ⟨x, hx, y, hy, e⟩ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 (G.V (.grid i 0))).1 h
      exact ⟨x, hx, y, hy, e, hA v hv x hx y hy e⟩
    obtain ⟨r₁, hr₁, hr₁P, g, hg, κ₁, hκ₁, e₁⟩ :=
      GlobalTheory.FinPl.placesToAdeles_all D (G.V (.grid i 0)) (G.Λ (.grid i 0)) (fun v => v ∉ G.pl.S0) hsd R h hoff
    obtain ⟨hdec, hcomm, -, -⟩ := (GlobalTheory.FinPl.localComponents D (fun v => v ∈ G.pl.S0)).2 (G.V (.grid i 0))
    obtain ⟨g₁, hg₁, g₂, hg₂, eg⟩ := hdec g
    have hin : ∀ x ∈ grpAt (G.V (.grid i 0)) (fun v => v ∉ G.pl.S0), x ∈ grpOff (G.V (.grid i 0)) (fun v => v ∈ G.pl.S0) :=
      fun x hx => congGrp_mono (idAt_le_idOff_compl (fun v => v ∈ G.pl.S0)) hx
    have hr₁off := hin r₁ hr₁P
    have hκ₁off := hin κ₁ hκ₁.1
    have hg₁off : g₁ ∈ grpOff (G.V (.grid i 0)) (fun v => ¬ v ∈ G.pl.S0) :=
      congGrp_mono (idAt_le_idOff_compl' (fun v => v ∈ G.pl.S0)) hg₁
    have hg₂off : g₂ ∈ grpOff (G.V (.grid i 0)) (fun v => ¬ v ∈ G.pl.S0) := by
      have : g₂ = g₁⁻¹ * g := by rw [eg]; group
      rw [this]
      exact mul_mem (inv_mem hg₁off) hg
    have c1 : r₁ * g₁ = g₁ * r₁ := (hcomm g₁ hg₁ r₁ hr₁off).symm
    have eh : h = g₁ * (r₁ * g₂ * κ₁) := by
      rw [e₁, eg, ← mul_assoc, ← mul_assoc, ← mul_assoc, c1]
    obtain ⟨r₀, hr₀, -, k₀, hk₀, hk₀S, ek⟩ := hB g₁ hg₁ _ (mul_mem (mul_mem hr₁off hg₂) hκ₁off) eh
    have c2 : k₀ * r₁ = r₁ * k₀ := hcomm k₀ hk₀S r₁ hr₁off
    have c3 : k₀ * g₂ = g₂ * k₀ := hcomm k₀ hk₀S g₂ hg₂
    refine ⟨r₀ * r₁, R.mul_mem hr₀ hr₁, g₂, mem_GinfC_of_off _ _ hg₂ hg₂off, k₀ * κ₁,
      mul_mem hk₀ (mem_lev_of_inK G _ hlat hκ₁), ?_⟩
    calc h = g₁ * (r₁ * g₂ * κ₁) := eh
      _ = r₀ * (k₀ * r₁) * g₂ * κ₁ := by rw [ek]; simp only [mul_assoc]
      _ = r₀ * r₁ * (k₀ * g₂) * κ₁ := by rw [c2]; simp only [mul_assoc]
      _ = r₀ * r₁ * g₂ * (k₀ * κ₁) := by rw [c3]; simp only [mul_assoc]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivEqZeroOfEven
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting
open scoped TensorProduct ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem unitary (D : D7) : Unitary D := by
  intro ψ S T χS χT om hW
  have hstd := hW.std
  obtain ⟨μ₀, 𝓕₀, h₀⟩ := GlobalTheory.ThetaAllChar.covolOneExists (D := D) S T
  refine ⟨⟨(μ₀, 𝓕₀), h₀⟩, fun q hq f₁ f₂ hf₁ hf₂ => ?_⟩
  have L := GlobalTheory.T.theta_inner_product_hermitian D ψ S T q.1 q.2 hstd hq f₁ f₂ hf₁ hf₂
  refine ⟨fun c => GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul c hf₁) hf₂, L.1, L.2.2.2.2.2.1,
    L.2.2.2.2.2.2.2, fun w => ⟨?_, (L.2.2.2.2.2.2.1 w).1⟩, fun p => ⟨hW.om_pres p f₁ hf₁, ?_⟩,
    GlobalTheory.T.continuous_nrm2_om_sub D ψ S T χS χT om q.1 q.2 hW hq f₁ f₂ hf₁ hf₂⟩
  · exact (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T).1 w f₁ hf₁
  · exact GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hW q.1 q.2 hq p f₁ f₂ hf₁ hf₂

theorem restrictedTensor (D : D7) : RestrictedTensor D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  have hstd := base_std hB
  have hinf := base_inf hB
  refine ⟨fun p f hf => ⟨((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hstd hinf f hf.1).2 p hf).1,
      GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace D ψ θ S T χS χT om sS sT ΛS ΛT hW hinf p f hf⟩,
    fun x hx => GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x hx, fun f hf ε hε => ?_,
    fun x f hx => ⟨fun w => GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx w,
      fun g h => GlobalTheory.T.weilRep_acts_on_pureTensors_placewise D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x f hx g h⟩⟩
  obtain ⟨f', hf', hlt⟩ := GlobalTheory.T.heisenberg_translates_span_dense_thetaFunctions D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ f hf ε hε
  refine ⟨f', Submodule.span_mono ?_ hf', hlt⟩
  rintro _ ⟨w, rfl⟩
  exact ⟨_, GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ (fun _ => f₀) f₀
    (GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ).1 w⟩

theorem coeffProduct (D : D7) : CoeffProduct D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x₁ f₁ x₂ f₂ h₁ h₂ g h
  exact GlobalTheory.T.pureTensor_innerProduct_eq_finprod_localInnerProducts D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ _ x₂ _ f₂
    (GlobalTheory.T.weilRep_acts_on_pureTensors_placewise D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x₁ f₁ h₁ g h) h₂

theorem cA_cA {D : D7} {e : AE D} {p : Place D} (h : e + cA D e = idem D p) : cA D (cA D e) = e := by
  have hp : cA D (idem D p) = idem D p := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p
  have h2 : cA D e + cA D (cA D e) = cA D e + e := by
    rw [← map_add, h, hp, ← h, add_comm]
  exact add_left_cancel h2

theorem isSplitIdem_cA {D : D7} {e : AE D} {p : Place D} (he : IsSplitIdem D e) (h : e + cA D e = idem D p) :
    IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, hε⟩ := he
  have hcc := cA_cA h
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hv, ?_⟩
  · rw [hcc, mul_comm, h2]
  · rw [hcc, add_comm, hε]

theorem splitModel (D : D7) : SplitModel D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v φ e he BS BT
  have hC := GlobalTheory.T.splitPlace_matrix_coordinate_on_half D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  refine ⟨(GlobalTheory.T.split_idempotent_base_function_identity D ψ θ S T sS sT ΛS ΛT f₀ hB v e he.1 he.2.1).1, fun Tm hTm => ?_⟩
  have M := GlobalTheory.T.schrodingerModel_coordinates_bijOn_and_weil_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v e e he.1 he.2.1 (Or.inl rfl)
    T.rank S.rank (mapCo φ S T BS BT) hC.1 Tm hTm
  rw [onHalf_eq_pull]
  exact ⟨M.1, fun ν hν => GlobalTheory.T.schrodingerModel_halfLatticeVolume_mul_inner_eq_inner D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v e he.1 T.rank S.rank
    (mapCo φ S T BS BT) hC.1 Tm hTm ν hν, fun g h hg hh x y hx hy Φ hΦ =>
    M.2 g h hg hh x y hx hy (grpCo φ S BS g) (grpCo φ T BT h) (fun t => hC.2 g h t) Φ hΦ⟩

theorem splitModelAdj (D : D7) : SplitModelAdj D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v φ e he BS BT
  have hC := GlobalTheory.T.splitPlaceAdjointMatrix_isCoordinate_equivariant D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  have hs : IsSplitIdem D (cA D e) := isSplitIdem_cA he.1 he.2.1
  have hsum : cA D e + cA D (cA D e) = idem D (.inl v) := by
    rw [cA_cA he.2.1, add_comm]
    exact he.2.1
  refine ⟨(GlobalTheory.T.split_idempotent_base_function_identity D ψ θ S T sS sT ΛS ΛT f₀ hB v (cA D e) hs hsum).1, fun Tm hTm => ?_⟩
  have M := GlobalTheory.T.schrodingerModel_coordinates_bijOn_and_weil_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v e (cA D e) he.1 he.2.1 (Or.inr rfl)
    S.rank T.rank (adjCo φ S T BS BT) hC.1 Tm hTm
  rw [onHalfAdj_eq_pull]
  exact ⟨M.1, fun ν hν => GlobalTheory.T.schrodingerModel_halfLatticeVolume_mul_inner_eq_inner D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v (cA D e) hs S.rank T.rank
    (adjCo φ S T BS BT) hC.1 Tm hTm ν hν, fun g h hg hh x y hx hy Φ hΦ =>
    M.2 g h hg hh x y hx hy (grpCo φ T BT h) (grpCo φ S BS g) (fun t => hC.2 g h t) Φ hΦ⟩

theorem deriv_eq_zero_of_even {c : ℝ → ℂ} {a : ℂ} (h : HasDerivAt c a 0) (he : ∀ t, c (-t) = c t) : a = 0 := by
  have hn : HasDerivAt (fun t : ℝ => -t) (-1) 0 := (hasDerivAt_id' (0 : ℝ)).neg
  have h0 : HasDerivAt c a (-(0 : ℝ)) := by rwa [neg_zero]
  have h1 := h0.scomp (0 : ℝ) hn
  have h2 : (c ∘ fun t : ℝ => -t) = c := funext fun t => he t
  rw [h2] at h1
  have h3 := h.unique h1
  rw [neg_one_smul] at h3
  linear_combination h3 / 2

private theorem exists_conj_mul_eq_mul {ι : Type*} {n : ℕ} (C C' : ι → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i, C i * C' i = 1)
    (s B : ι → Matrix (Fin n) (Fin n) ℂ) :
    ∃ s' B' : ι → Matrix (Fin n) (Fin n) ℂ, (∀ i, s' i * C i = C i * s i) ∧ ∀ i, B' i = C i * B i := by
  refine ⟨fun i => C i * s i * C' i, fun i => C i * B i, fun i => ?_, fun i => rfl⟩
  have h' : C' i * C i = 1 := mul_eq_one_comm.mp (h i)
  simp only [Matrix.mul_assoc, h', Matrix.mul_one]

theorem fockModel (D : D7) : FockModel D := by
  intro ψ θ S T χS χT om hW hθ τ
  obtain ⟨mS, mT, hm⟩ := GlobalTheory.T.fockVacuum_maximalCompact_character_realPlace D ψ θ S T χS χT om hW hθ τ
  refine ⟨mS, mT, ?_⟩
  intro sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT f hf hvac P
  have hstd := hW.std
  have hPT : ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q) := by
    intro Q
    obtain ⟨sS', BS', hS', hBS'⟩ := exists_conj_mul_eq_mul _ _
      (fun ρ => GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) ρ (1 : GA D S)) sS BS
    obtain ⟨sT', BT', hT', hBT'⟩ := exists_conj_mul_eq_mul _ _
      (fun ρ => GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) ρ (1 : GA D T)) sT BT
    exact (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS' BS BS' sT sT' BT BT' 1 1
      hS' hT' hBS' hBT' f hf Q).1
  obtain ⟨μ₀, 𝓕₀, h₀⟩ := GlobalTheory.ThetaAllChar.covolOneExists (D := D) S T
  refine ⟨hPT P, fun μ 𝓕 hμ Q => GlobalTheory.T.fockVectors_inner_eq_fockInnerProduct_mul_norm D ψ θ S T hstd hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT
      f hf hvac μ 𝓕 hμ P Q,
    fun κS κT hκS hκT g h hg hh => GlobalTheory.T.maximalCompact_acts_on_fockVectors_by_substitution D ψ θ S T χS χT om hW hθ sS BS sT BT pS pT hpS hpT hsS hsT
      hBS hBT f hf τ κS κT hκS hκT g h hg hh _
      (hm sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT f hf hvac κS κT hκS hκT g h hg hh) P,
    fun YS YT hYS hYT w => ?_⟩
  have hL := GlobalTheory.T.fockVacuum_matrixCoefficient_even D ψ θ S T χS χT om hW hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT τ YS YT hYS hYT
  obtain ⟨Gn, hGn⟩ := GlobalTheory.T.exists_weilDatum_oneParameter_generator_commutators D ψ θ S T χS χT om hW hθ τ _ hL.1 _ hL.2.1

  have key := GlobalTheory.T.fock_operator_acts_by_noncompact_quadratic_ops D ψ θ S T hstd hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT τ YS YT hYS hYT μ₀ 𝓕₀ h₀ Gn
    (fun f' hf' => ⟨(hGn f' hf').1, (hGn f' hf').2.1, (hGn f' hf').2.2.1⟩) f hf hvac
    (fun g hg hgv => deriv_eq_zero_of_even ((hGn f hf).2.2.2.2 μ₀ 𝓕₀ h₀ g hg)
      (fun t => hL.2.2 f g hf hvac hg hgv μ₀ 𝓕₀ h₀ t)) P
  rw [← key]
  exact (hGn _ (hPT P)).2.2.2.1 w

theorem placeModels : ∀ D : D7, PlaceModels D := fun D =>
  ⟨unitary D, restrictedTensor D, coeffProduct D, splitModel D, splitModelAdj D, GlobalTheory.T.splitPlace_thetaLattice_halves_selfDual_frames D, GlobalTheory.T.inert_place_stabilizers_fix_weil_lattice_vacuum D,
    GlobalTheory.T.splitPlace_latticeStabilisers_fix_weilVacuum D, fockModel D, GlobalTheory.T.fockVectors_pureTensors D, GlobalTheory.T.definiteThetaLift_localVector D, GlobalTheory.T.thetaChainStepVector_localPureTensor D⟩

end GlobalTheory.PlaceTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanOperatorWeilRepPureTensor
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

open GlobalTheory.ArchFactor in

theorem GlobalTheory.ArchFactorPair.exists_archOperator_pair :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ h ∈ UAt σ W (evI F), ∃ T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f (T f) := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hstd _ _ _ _ _ _ _ _ hweil h hh
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hweil
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om (1, h) Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (1, h) Φ hΦ
  have h1 : (1 : UA σ X.J) ∈ UAt σ X (evI F) := by
    intro u _
    simp [mat]
  have hcomm := comm_offI hweil (1, h) h1 hh
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_finiteWeight_complementary_archimedeanSchwartz (F := F) (Fin n × Fin d)
  have hB : ∀ f : SInf F (Fin n × Fin d), ∃ g : SInf F (Fin n × Fin d),
      ∀ t, g t = (R 0)⁻¹ * om (1, h) (tens (evI F) (⇑f) R) (liftI t) := by
    intro f
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_schwartz_archimedeanSlice_adelicSchwartz _ (Submodule.smul_mem _ (R 0)⁻¹ (hkeep _ (hR f).2))
    exact ⟨g, fun t => by rw [hg]; rfl⟩
  choose Tf hTf using hB
  have htens_add : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) (⇑(f + g)) R = tens (evI F) (⇑f) R + tens (evI F) (⇑g) R := by
    intro f g; funext x; simp only [tens, SchwartzMap.add_apply, Pi.add_apply]; ring
  have htens_smul : ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)),
      tens (evI F) (⇑(c • f)) R = c • tens (evI F) (⇑f) R := by
    intro c f; funext x; simp only [tens, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul]; ring
  let T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) :=
    { toFun := Tf
      map_add' := fun f g => by
        ext t
        rw [SchwartzMap.add_apply, hTf, hTf, hTf, htens_add, map_add, Pi.add_apply]; ring
      map_smul' := fun c f => by
        ext t
        rw [SchwartzMap.smul_apply, hTf, hTf, htens_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          RingHom.id_apply]; ring }
  refine ⟨T, fun f r hr => ?_⟩
  funext y
  set T0 := om (1, h) with hT0
  set u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) with hudef
  have hu : evI F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  set p : Fin n × Fin d → AF F := liftI (fun i => evI F (y i)) with hpdef
  have hyp : y + u • (-y) = p := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef, liftI, evI,
      RingEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_
    · show (y i).1 + 0 * (-(y i)).1 = (y i).1
      simp
    · show (y i).2 + 1 * (-(y i)).2 = 0
      rw [one_mul]
      exact add_neg_cancel ((y i).2)
  have hpat : At (evI F) p := by
    intro u' hu'
    have h0 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu')
    funext i
    refine Prod.ext ?_ ?_
    · show u'.1 * (p i).1 = 0
      rw [h0, zero_mul]
    · show u'.2 * (p i).2 = 0
      simp [hpdef, liftI]
  set Φ₀ := tens (evI F) (⇑f) R with hΦ₀
  set Φ₁ := tens (evI F) (⇑f) r with hΦ₁
  set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR f).2
  have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hfz : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
    have hpz : At (evI F) (p + z) := fun u' hu' => by
      rw [smul_add, hpat u' hu', hz u' hu', add_zero]
    have e3 : R (p + z) = R 0 := by simpa using (hR f).1 0 (p + z) hpz
    have e4 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add', evI_mul', hu, zero_mul, add_zero]
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
    rw [e4, e2, e3, e1]
    field_simp
    ring
  have h0 := GlobalTheory.T.heisenbergCommuting_operator_independent_of_archimedeanFibres ψ T0 hstd hkeep (fun u hu p q Φ hΦ => hcomm u hu p q Φ hΦ) (Φ₁ - Φ₂)
    (sub_mem hr.2 hm₂) y hfz
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have htr : T0 (fun w => Φ₀ (w + u • (-y))) = fun w => T0 Φ₀ (w + u • (-y)) := by
    have h := hcomm u hu (-y) 0 Φ₀ hm₀
    rw [smul_zero, schr_trans', schr_trans'] at h
    exact h
  have h2 : T0 Φ₂ y = (r y / R 0) * T0 Φ₀ p := by
    rw [hΦ₂, map_smul, htr, Pi.smul_apply, smul_eq_mul, hyp]
  show T0 Φ₁ y = tens (evI F) (⇑(Tf f)) r y
  rw [h0, h2]
  show r y / R 0 * T0 Φ₀ p = (Tf f) (fun i => evI F (y i)) * r y
  rw [hTf]
  show r y / R 0 * T0 Φ₀ p = (R 0)⁻¹ * T0 Φ₀ p * r y
  rw [div_eq_mul_inv]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEtaleCoverListingHeckeKernelSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_cover_listing_heckeKernelScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo P p i), admitted l P p → ∀ (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk), ∃ (T' : Type) (_ : CommRing T') (_ : Algebra T T') (n : ℕ) (σ : Fin n → (Sp T' ⟶ Xo.univ.t.G.left)), Algebra.Etale T T' ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap T T')) ∧ (∀ j, σ j ≫ Xo.univ.t.G.hom = spMap (algebraMap T T') ≫ h ≫ Z.π₁) ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T' →+* Ω) (x₁ : Sp Ω ⟶ Xo.X) (C : Subgroup (Over.mk x₁ ⟶ Xo.univ.t.G)), Z.Carries (spMap χ ≫ spMap (algebraMap T T') ≫ h) x₁ C → ∃ e : Fin n ≃ C, ∀ j, (e j).1.left = spMap χ ≫ σ j := by
  first | exact @GlobalTheory.HeckeEx.exists_etale_cover_lists_kerScheme | exact GlobalTheory.HeckeEx.exists_etale_cover_lists_kerScheme | (intros; apply GlobalTheory.HeckeEx.exists_etale_cover_lists_kerScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodRationalSchroedingerModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_rational_schroedingerModel : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    ∀ {n d : ℕ} (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ),
    V.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
    ∀ (μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)) (dom : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)),
      μ.IsHaarMeasure → IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig V.J) dom μ →
    ∃ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig V Ws, M.μ = μ ∧ M.dom = dom ∧ M.IsGood Bs.ψ := by
  first | exact @GlobalTheory.SquareAgree.exists_good_model | exact GlobalTheory.SquareAgree.exists_good_model | (intros; apply GlobalTheory.SquareAgree.exists_good_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealComponentFrameHomUnitaryDiagStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realComponent_frame_hom_unitaryDiag : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∃ E : GA D V →* Formalism.REAL.UJ (M.ε τ), ∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ := by
  first | exact @GlobalTheory.FibreAtTau.cmp_frame_hom | exact GlobalTheory.FibreAtTau.cmp_frame_hom | (intros; apply GlobalTheory.FibreAtTau.cmp_frame_hom <;> assumption)
end

