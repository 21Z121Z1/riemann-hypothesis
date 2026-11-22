import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairGluing.ExistsDenLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentMulNatPowOfMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpFullImp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlancherelSchrodingerIntertwiner
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicIdentification
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinAdIdent

variable {D : D7}

theorem mem_iff_of_image {A : Type} [CommRing A] {m n : ℕ} {j : Matrix (Fin m) (Fin n) A} (hj : Function.Injective j.mulVec)
    {H : Set (Fin n → A)} {H' : Set (Fin m → A)} (h : j.mulVec '' H = H') (y : Fin n → A) : y ∈ H ↔ j.mulVec y ∈ H' := by
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rwa [← hj hzy]

theorem level_conj {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (ψ : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ψ.comp σ = τ.comp ψ) {S : Subring B} (H : Submodule S (Fin n → B)) (H' : Submodule S (Fin m → B))
    {j : Matrix (Fin m) (Fin n) A} (hb : Function.Bijective (j.map ψ).mulVec)
    (hl : (j.map ψ).mulVec '' (H : Set _) = (H' : Set _)) {J : Matrix (Fin n) (Fin n) A} {J' : Matrix (Fin m) (Fin m) A}
    {x : GL (Fin n) A} {x' : GL (Fin m) A} (hx : x ∈ Formalism.UG.UJ σ J) (hx' : x' ∈ Formalism.UG.UJ σ J') (hc : x'.val * j = j * x.val) :
    Formalism.UG.bc ψ x ∈ Formalism.UG.level τ (J.map ψ) H ↔ Formalism.UG.bc ψ x' ∈ Formalism.UG.level τ (J'.map ψ) H' := by
  have hu : ∀ {k : ℕ} {K : Matrix (Fin k) (Fin k) A} {z : GL (Fin k) A}, z ∈ Formalism.UG.UJ σ K →
      Formalism.UG.bc ψ z ∈ Formalism.UG.UJ τ (K.map ψ) := by
    intro k K z hz
    have hz' : Formalism.UG.cT σ (z : Matrix (Fin k) (Fin k) A) * K * z = K := hz
    show Formalism.UG.cT τ ((z : Matrix (Fin k) (Fin k) A).map ψ) * K.map ψ * (z : Matrix (Fin k) (Fin k) A).map ψ = K.map ψ
    conv_rhs => rw [← hz']
    simp only [Matrix.map_mul]
    congr 2
    ext a b
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
    exact (RingHom.congr_fun h _).symm
  obtain ⟨j', hj1, -⟩ := exists_inv hb
  have hcψ : x'.val.map ψ * j.map ψ = j.map ψ * x.val.map ψ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hc]
  have key := stab_pred (p := fun y => y ∈ H) (p' := fun y => y ∈ H') hj1 hcψ (mem_iff_of_image hb.1 hl)
  have e1 : Formalism.UG.bc ψ x ∈ Formalism.UG.level τ (J.map ψ) H ↔ Formalism.UG.bc ψ x ∈ Formalism.UG.UJ τ (J.map ψ) ∧
      ∀ y, y ∈ H ↔ (x.val.map ψ).mulVec y ∈ H := Iff.rfl
  have e2 : Formalism.UG.bc ψ x' ∈ Formalism.UG.level τ (J'.map ψ) H' ↔ Formalism.UG.bc ψ x' ∈ Formalism.UG.UJ τ (J'.map ψ) ∧
      ∀ y, y ∈ H' ↔ (x'.val.map ψ).mulVec y ∈ H' := Iff.rfl
  rw [e1, e2]
  exact ⟨fun a => ⟨hu hx', key.1 a.2⟩, fun a => ⟨hu hx, key.2 a.2⟩⟩

theorem levelVL_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ} (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (Λ' : Submodule (𝓞 E) (Fin m → E))
    (G : Matrix (Fin n) (Fin n) E) (G' : Matrix (Fin m) (Fin m) E) (j : Matrix (Fin m) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hb : Function.Bijective (j.map (Formalism.UG.prV (E := E) v)).mulVec)
    (hl : (j.map (Formalism.UG.prV (E := E) v)).mulVec '' (Formalism.L2.Herm.locL v Λ : Set _) = (Formalism.L2.Herm.locL v Λ' : Set _))
    {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {x' : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ Formalism.UG.UPts σ G (Formalism.L2.Herm.Af F)) (hx' : x' ∈ Formalism.UG.UPts σ G' (Formalism.L2.Herm.Af F))
    (hc : x'.val * j = j * x.val) :
    Formalism.UG.bc (Formalism.UG.prV v) x ∈ Formalism.UG.levelVL σ G v Λ ↔ Formalism.UG.bc (Formalism.UG.prV v) x' ∈ Formalism.UG.levelVL σ G' v Λ' := by
  have h1 := level_conj (Formalism.UG.prV (E := E) v) (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) (Formalism.UG.sigR σ (v.adicCompletion F))
    (Formalism.UG.P.afsplit_prV_comp_sigR σ v) (Formalism.L2.Herm.locL v Λ) (Formalism.L2.Herm.locL v Λ') hb hl hx hx' hc
  have hG : ∀ {k : ℕ} (K : Matrix (Fin k) (Fin k) E),
      (K.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))).map (Formalism.UG.prV (E := E) v) =
        K.map (Formalism.UG.inclE (F := F) (v.adicCompletion F)) := by
    intro k K
    ext a b
    simp only [Matrix.map_apply]
    exact Formalism.UG.P.afsplit_prV_inclE v (K a b)
  rw [hG, hG] at h1
  exact h1

open GlobalTheory.HeckeTrans in
set_option maxHeartbeats 800000 in
theorem link_of_isLatIsom {V V' : HSp D} (h : V.rank = V'.rank)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)}
    {β : GL (Fin V.rank) (EAf D)} {β' : GL (Fin V'.rank) (EAf D)} {N N' : ℕ}
    (hβ : IsSDFrame V β Λ N) (hβ' : IsSDFrame V' β' Λ' N') {j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)}
    {j' : Matrix (Fin V.rank) (Fin V'.rank) (EAf D)} (hj : IsLatIsom V V' Λ Λ' j) (h1 : mmul j j' = 1) (h2 : mmul j' j = 1)
    {φ : GfC V ≃ₜ* GfC V'} (hφ : IsConjBy V V' j φ) :
    Link V V' (N * N') φ.toMulEquiv (j.map (unswap D)) (j'.map (unswap D)) := by
  obtain ⟨c, hB⟩ := hβ
  obtain ⟨c', hB'⟩ := hβ'
  have himg : ∀ x, x ∈ (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set _) ↔
      j.mulVec x ∈ (Formalism.L2.Herm.hatL (F := D.host.F) Λ' : Set _) :=
    mem_iff_of_image hj.1.1.1 hj.2
  have hvec : ∀ (f : Af D.host.F ⊗[D.host.F] D.host.E) (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E),
      (fun a => swapAE D (f * ((j.map (unswap D)).mulVec y) a)) = j.mulVec (fun b => swapAE D (f * y b)) := by
    intro f y
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul, swap_unswap]
    exact Finset.sum_congr rfl fun b _ => by ring
  have gN : ∀ f, Good (D := D) (N * N') f → Good (N ^ c) f := fun f hf => hf.pow c
  have gN' : ∀ f, Good (D := D) (N * N') f → Good (N' ^ c') f := by
    intro f hf
    rw [mul_comm] at hf
    exact hf.pow c'
  refine ⟨h, GlobalTheory.HeckeTrans.map_mul_one _ h1, GlobalTheory.HeckeTrans.map_mul_one _ h2, ?_, ?_, ?_, ?_⟩
  · intro g
    have := congrArg (fun X => X.map (unswap D)) (hφ g)
    simp only [mmul, Matrix.map_mul, finE_unswap] at this
    exact this
  · intro f hf y
    rw [(lamHat_good hB (gN f hf)).2, (lamHat_good hB' (gN' f hf)).2, hvec]
    exact himg _
  · intro f hf y hy
    exact (lamHat_good hB (gN f hf)).1 y hy
  · intro f hf y hy
    exact (lamHat_good hB' (gN' f hf)).1 y hy

theorem corr_inA {V V' : HSp D} (φ : GfC V ≃ₜ* GfC V') (R : Finset (GfC V)) :
    Corr φ.toMulEquiv (inA V R : Set (GA D V)) (imA φ R : Set (GA D V')) := by
  refine ⟨?_, ?_, fun g => ?_⟩
  · intro g hg
    simp only [inA, Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe] at hg
    obtain ⟨a, -, rfl⟩ := hg
    exact a.2
  · intro g hg
    simp only [imA, inA, Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe] at hg
    obtain ⟨a, -, rfl⟩ := hg
    exact a.2
  · simp [inA, imA]
    exact ⟨fun hg => ⟨g.1, g.2, hg, rfl⟩, fun ⟨a, ha, hR, hag⟩ => hag ▸ hR⟩

theorem chi_symm {G G' : Type} [Group G] [Group G'] {H : Subgroup G} {H' : Subgroup G'} {φ : H ≃* H'} {K : Set G} {K' : Set G'}
    (hK : Corr φ K K') {χ : G → ℂ} {χ' : G' → ℂ} (hχ : ∀ g : H, (g : G) ∈ K → χ' (φ g : G') = χ g) (g : H')
    (hg : (g : G') ∈ K') : χ (φ.symm g : G) = χ' g := by
  have h1 : ((φ.symm g : H) : G) ∈ K := (hK.2.2 (φ.symm g)).2 (by simpa using hg)
  have h2 := hχ (φ.symm g) h1
  simpa using h2.symm

private theorem finE_mem_UPts (V : HSp D) (g : GA D V) :
    finE V g ∈ Formalism.UG.UPts D.sp.cm.sig V.gram (Formalism.L2.Herm.Af D.host.F) := by
  have hg : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) ((matHom V g : GL _ _) : Matrix _ _ _) *
      JR (AF D.host.F) V.gram * ((matHom V g : GL _ _) : Matrix _ _ _) = JR (AF D.host.F) V.gram := g.2
  show Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) ((finE V g : GL _ _) : Matrix _ _ _) *
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * ((finE V g : GL _ _) : Matrix _ _ _) =
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))
  have := congrArg (fun X => X.map (GlobalTheory.FinIsoGrp.qFin D)) hg
  simp only [Matrix.map_mul] at this
  rw [GlobalTheory.FinIsoGrp.finE_val, ← GlobalTheory.FinIsoGrp.gram_map, ← this]
  congr 2
  ext a b
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.FinIsoGrp.qFin_sig]

set_option maxHeartbeats 1600000 in
theorem inducedIso (D : D7) : InducedIso D := by
  intro V V' h Λ Λ' β β' N N' hβ hβ' T j hj hm
  obtain ⟨j', h1, h2⟩ := exists_inv hj.1.1
  obtain ⟨φ, hφ⟩ := GlobalTheory.FinIsoGrp.exists_finIso V V' j j' h1 h2 hj.1.2
  have hφ' : IsConjBy V V' j φ := hφ
  have L := link_of_isLatIsom h hβ hβ' hj h1 h2 hφ'
  obtain ⟨c, hB⟩ := id hβ
  obtain ⟨c', hB'⟩ := id hβ'
  obtain ⟨u, hu, hT⟩ := hm
  have hl : ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ', j'.mulVec y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    ((image_iff h1 h2 _ _).1 hj.2).2
  have e : ∀ {W : HSp D} (γ : GL (Fin W.rank) (EAf D)) (L1 : Formalism.L2.DIV.LevDat D.host.E ℂ W.rank) (κ : GA D W),
      κ ∈ levG W γ L1 ↔ κ ∈ GfC W ∧ finE W κ ∈ Formalism.L2.DIV.parLev D.sp.cm W.gram γ L1 ∧
        Formalism.L2.DIV.rTup γ L1 (finE W κ) ∈ L1.P.H := fun _ _ _ => Iff.rfl
  have hle := fun (L0 : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hL0 : ReadIn L0 T) (g : GfC V) =>
    lev_eq h V.gram V'.gram Λ Λ' β (finE V g) β' (finE V' (φ g)) hB.1 hB'.1 j j' h1 h2 hl u hu T hT (hφ g)
      (finE_mem_UPts V g) (finE_mem_UPts V' (φ g)) L0 hL0
  have hlev : ∀ L0 : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L0 T → ∀ g : GfC V,
      (g : GA D V) ∈ levG V β L0 ↔ (φ g : GA D V') ∈ levG V' β' (castDat h L0) := by
    intro L0 hL0 g
    have H := hle L0 hL0 g
    rw [e, e]
    constructor
    · rintro ⟨-, hp, hr⟩
      exact ⟨(φ g).2, H.1.1 hp, (H.2 hp).1 ▸ hr⟩
    · rintro ⟨-, hp', hr'⟩
      have hp := H.1.2 hp'
      exact ⟨g.2, hp, (H.2 hp).1 ▸ hr'⟩
  have hchi : ∀ L0 : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L0 T → ∀ g : GfC V, (g : GA D V) ∈ levS V β L0 →
      levChi V' β' (castDat h L0) (φ g : GA D V') = levChi V β L0 (g : GA D V) := by
    intro L0 hL0 g hg
    have hp := ((e β L0 g).1 hg).2.1
    have H := (hle L0 hL0 g).2 hp
    unfold levChi
    rw [H.2]
  have hK : ∀ L0 : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L0 T →
      Corr φ.toMulEquiv (levS V β L0) (levS V' β' (castDat h L0)) := fun L0 hL0 =>
    ⟨fun g hg => ((e β L0 g).1 hg).1, fun g hg => ((e β' (castDat h L0) g).1 hg).1, fun g => hlev L0 hL0 g⟩
  refine ⟨φ, hφ', ?_⟩
  exact {
    stabLoc := fun v g => by
      obtain ⟨hb, hl'⟩ := loc_gen D.sp.cm.sig v Λ Λ' V.gram V'.gram j hj.1.1 hj.1.2 hj.2
      exact levelVL_conj D.sp.cm.sig v Λ Λ' V.gram V'.gram j hb.1 hl' (finE_mem_UPts V g) (finE_mem_UPts V' (φ g)) (hφ g)
    supp := fun f g => L.supp f g
    det := fun g => L.det g
    lev := hlev
    chi := hchi
    lift := fun L0 hL0 g0 g => by
      have H := hle L0 hL0 g
      unfold IsLevelLift
      constructor
      · rintro ⟨-, hp, hr⟩
        exact ⟨(φ g).2, H.1.1 hp, (H.2 hp).1.trans hr⟩
      · rintro ⟨-, hp', hr'⟩
        have hp := H.1.2 hp'
        exact ⟨g.2, hp, (H.2 hp).1.symm.trans hr'⟩
    sph := fun S hS g => ⟨L.sph_imp S hS g, fun hg => by simpa using L.symm.sph_imp S hS (φ g) hg⟩
    heckeElt := fun P e ϖ k hM he g =>
      ⟨L.hecke_imp he hM g, fun hg => by simpa using L.symm.hecke_imp he hM (φ g) hg⟩
    heckeAt := fun P k hM g => by
      unfold IsHeckeAt
      constructor
      · rintro ⟨e, ϖ, he, h1', h2', h3⟩
        exact ⟨e, ϖ, he, h1', h2', L.hecke_imp he hM g h3⟩
      · rintro ⟨e, ϖ, he, h1', h2', h3⟩
        exact ⟨e, ϖ, he, h1', h2', by simpa using L.symm.hecke_imp he hM (φ g) h3⟩
    divAt := fun P e f ϖ d hM hP g =>
      ⟨L.div_imp hP hM g, fun hg => by simpa using L.symm.div_imp hP hM (φ g) hg⟩
    opAt := fun L0 hL0 S P k hM R =>
      ⟨fun H => L.opAt_imp (hK L0 hL0) (hchi L0 hL0) (corr_inA φ R) S hM H,
        fun H => L.symm.opAt_imp (hK L0 hL0).symm (chi_symm (hK L0 hL0) (hchi L0 hL0)) (corr_inA φ R).symm S hM H⟩
    opFull := fun L0 hL0 S P d hM R =>
      ⟨fun H => L.opFull_imp (hK L0 hL0) (hchi L0 hL0) (corr_inA φ R) S hM H,
        fun H => L.symm.opFull_imp (hK L0 hL0).symm (chi_symm (hK L0 hL0) (hchi L0 hL0)) (corr_inA φ R).symm S hM H⟩ }

end GlobalTheory.FinAdIdent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlancherelSchrodingerIntertwinerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_plancherel_schrodinger_intertwiner_alt : ∀ {X Aψ G : Type} [AddCommGroup X] [AddCommGroup Aψ] [AddCommGroup G] [Fintype G]
  (ψ : AddChar Aψ ℂ) (B : X → X → Aψ) (Λc : AddSubgroup X) (red : Λc →+ G)
  (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hs : X → (X → ℂ) → (X → ℂ)) (SB : (X → ℂ) → Prop) (Hd : X → Prop)
  (Th : (X → ℂ) → Prop) (ip : (X → ℂ) → (X → ℂ) → ℂ) (f₀ : X → ℂ) (Gd : G → ℂ),
  Function.Surjective red →
  (∀ t k y, B (t + k) y = B t y + B k y) →
  (∀ Ψ : X → ℂ, (∀ t, Ψ t ≠ 0 → t ∈ Λc) → (∀ t, ∀ u ∈ Λc, Ψ (t + Fintype.card G • u) = Ψ t) → SB Ψ) →
  (∀ Φ, SB Φ → ∀ x ∈ Λc, T (fun t => Φ (t + x)) = hs x (T Φ)) →
  (∀ Φ, SB Φ → ∀ y, Hd y → T (fun t => ψ (B t y) * Φ t) = hs y (T Φ)) →
  T (fun t => if t ∈ Λc then 1 else 0) = f₀ →
  (∀ x : Λc, red x ≠ 0 → ∃ y, Hd y ∧ (∀ k : Λc, red k = 0 → ψ (B k y) = 1) ∧ ψ (B x y) ≠ 1) →
  (∀ w (a : ℂ) (f₁ f₂ : X → ℂ), hs w (a • f₁ + f₂) = a • hs w f₁ + hs w f₂) →
  (∀ (a : ℂ) f₁ f₂, Th f₁ → Th f₂ → Th (a • f₁ + f₂)) →
  (∀ w f, Th f → Th (hs w f)) →
  (∀ (a : ℂ) f₁ f₂ g, Th f₁ → Th f₂ → Th g → ip (a • f₁ + f₂) g = a * ip f₁ g + ip f₂ g) →
  (∀ f g, Th f → Th g → ip g f = starRingEnd ℂ (ip f g)) →
  (∀ w f₁ f₂, Th f₁ → Th f₂ → ip (hs w f₁) (hs w f₂) = ip f₁ f₂) →
  Th f₀ → ip f₀ f₀ = 1 →
  ip (T fun t => if h : t ∈ Λc then Gd (red ⟨t, h⟩) else 0) (T fun t => if h : t ∈ Λc then Gd (red ⟨t, h⟩) else 0) =
    ((∑ g, ‖Gd g‖ ^ 2 : ℝ) : ℂ) / (Fintype.card G : ℂ) := by
  first | exact @GlobalTheory.finite_plancherel_schrodinger_intertwiner | exact GlobalTheory.finite_plancherel_schrodinger_intertwiner | (intros; apply GlobalTheory.finite_plancherel_schrodinger_intertwiner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesClosed

variable {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

def lowPart {m : ℕ} (M : Mx D m m) : Mx D m m := Matrix.of fun i j => if j ≤ i then M i j else 0

theorem continuous_lowPart {m : ℕ} : Continuous (lowPart (D := D) (m := m)) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun a : Mx D m m => if j ≤ i then a i j else 0
    split_ifs
    · exact (continuous_apply j).comp (continuous_apply i)
    · exact continuous_const

theorem lowPart_eq_iff {m : ℕ} (M : Mx D m m) :
    lowPart M = lowPart 1 ↔ ∀ i j : Fin m, (j < i → M i j = 0) ∧ M i i = 1 := by
  constructor
  · intro h i j
    refine ⟨fun hji => ?_, ?_⟩
    · have := congrFun (congrFun h i) j
      simp only [lowPart, Matrix.of_apply, if_pos hji.le] at this
      rwa [Matrix.one_apply_ne hji.ne'] at this
    · have := congrFun (congrFun h i) i
      simp only [lowPart, Matrix.of_apply, if_pos (le_refl i), Matrix.one_apply_eq] at this
      exact this
  · intro h
    ext i j
    simp only [lowPart, Matrix.of_apply]
    split_ifs with hji
    · rcases hji.lt_or_eq with hlt | heq
      · rw [(h i j).1 hlt, Matrix.one_apply_ne hlt.ne']
      · subst heq; rw [(h j j).2, Matrix.one_apply_eq]
    · rfl

theorem strictUp_sub_one {m : ℕ} {M : Mx D m m} (h : ∀ i j : Fin m, (j < i → M i j = 0) ∧ M i i = 1) :
    GlobalTheory.BesselChar.StrictUp (M - 1) := by
  intro j i hij
  rcases hij.lt_or_eq with hlt | heq
  · rw [Matrix.sub_apply, (h j i).1 hlt, Matrix.one_apply_ne hlt.ne', sub_zero]
  · subst heq; rw [Matrix.sub_apply, (h i i).2, Matrix.one_apply_eq, sub_self]

theorem mem_jacGrp_iff_mat (g : GA D S) : g ∈ jacGrp d ↔
    (d.p0 ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.jX) = 0 ∧
      ∀ i j : Fin ρ, (j < i → (d.pX ⬝ (mt S g ⬝ d.jX)) i j = 0) ∧ (d.pX ⬝ (mt S g ⬝ d.jX)) i i = 1) := by
  constructor
  · intro hg
    obtain ⟨n, hn, h, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.1 g).1 hg
    obtain ⟨u, hu, b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
    have e : mt S (d.levi u * (d.nB b * d.nC c) * d.emb0 h) ⬝ d.jX = d.jX ⬝ u.1 := by
      rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, GlobalTheory.MixPer.Decomp.mt_flag_jX]
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_jX, d.pY_jX, d.pX_jX, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.one_mul]
    exact ⟨rfl, rfl, fun i j => hu i j⟩
  · rintro ⟨h0, hY, hX⟩
    obtain ⟨u, hu, hu1⟩ := GlobalTheory.MixPer.Decomp.exists_unit (strictUp_sub_one hX)
    have hu' : u.1 = d.pX ⬝ (mt S g ⬝ d.jX) := by rw [hu1, add_sub_cancel]
    have hgX : mt S g ⬝ d.jX = d.jX ⬝ u.1 := by
      rw [hu']
      conv_lhs => rw [GlobalTheory.MixPer.Decomp.decomp d (mt S g ⬝ d.jX)]
      rw [h0, hY, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero]
    have hst : (d.levi u)⁻¹ * g ∈ stabX d := mem_fixer.2 (GlobalTheory.MixPer.Decomp.fix_of_eq (by rw [d.levi_jX, hgX]))
    obtain ⟨n, hn, h, hnh⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.1 _).1 hst
    have hn' : n ∈ flagN d := (Subgroup.mem_inf.1 (show n ∈ flagN d ⊓ fixer S d.jX from hn)).1
    have e : g = d.levi u * n * d.emb0 h := by rw [mul_assoc, ← hnh, mul_inv_cancel_left]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem (d.levi_mem_NFlag hu) hn')) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem jacGrp_closed : IsClosed (jacGrp d : Set (GA D S)) := by
  haveI : T2Space (Mx D S₀.rank ρ) := (lattice_Mx D _ _).2.2.2.1
  haveI : T2Space (Mx D ρ ρ) := (lattice_Mx D _ _).2.2.2.1
  have hc : Continuous fun g : GA D S => mt S g ⬝ d.jX := (continuous_mt S).matrix_mul continuous_const
  have e : (jacGrp d : Set (GA D S)) = {g | d.p0 ⬝ (mt S g ⬝ d.jX) = 0} ∩ {g | d.pY ⬝ (mt S g ⬝ d.jX) = 0} ∩
      {g | lowPart (d.pX ⬝ (mt S g ⬝ d.jX)) = lowPart 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_jacGrp_iff_mat, Set.mem_inter_iff, Set.mem_setOf_eq, lowPart_eq_iff, and_assoc]
  rw [e]
  exact ((isClosed_eq (continuous_const.matrix_mul hc) continuous_const).inter
    (isClosed_eq (continuous_const.matrix_mul hc) continuous_const)).inter
    (isClosed_eq (continuous_lowPart.comp (continuous_const.matrix_mul hc)) continuous_const)

theorem flagUnipotent_anisotropic_projection_eq_one {n : GA D S} (hn : n ∈ flagN d) : d.p0 ⬝ (mt S n ⬝ d.j0) = 1 := by
  obtain ⟨u, -, b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
  rw [mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]
  rw [d.nC_j0, d.nB_j0, ← Matrix.mul_assoc d.p0 (mt S (d.levi u)), d.wittDecomp_projAnisotropic_levi, Matrix.mul_add, d.p0_j0,
    ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]

theorem witt_anisotropic_block_flag_mul_embedded {n : GA D S} (hn : n ∈ flagN d) (k : GA D S₀) :
    d.p0 ⬝ (mt S (n * d.emb0 k) ⬝ d.j0) = mt S₀ k := by
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt S n) d.j0, ← Matrix.mul_assoc d.p0, flagUnipotent_anisotropic_projection_eq_one d hn,
    Matrix.one_mul]

set_option maxHeartbeats 1000000 in

theorem exists_emb_of_fix {k : GA D S₀} (hk : mt S₀ k ⬝ o.jB = o.jB) : ∃ a : GA D A, o.emb (a, 1) = k := by
  have h1 : o.pB ⬝ (mt S₀ k ⬝ o.jA) = 0 := by
    have e : adj o.jB ⬝ (gA S₀ ⬝ (mt S₀ k ⬝ o.jA)) = 0 := by
      conv_lhs => rw [← hk]
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S₀) (mt S₀ k) o.jA,
        ← Matrix.mul_assoc (adj (mt S₀ k)) (gA S₀ ⬝ mt S₀ k) o.jA, mt_unitary, o.gram_BA]
    rw [o.pB_eq, Matrix.mul_assoc, Matrix.mul_assoc, e, Matrix.mul_zero]
  obtain ⟨M, hM⟩ : ∃ M : Mx D A.rank A.rank, M = o.pA ⬝ (mt S₀ k ⬝ o.jA) := ⟨_, rfl⟩
  have hA : mt S₀ k ⬝ o.jA = o.jA ⬝ M := by
    calc mt S₀ k ⬝ o.jA = (o.jA ⬝ o.pA + o.jB ⬝ o.pB) ⬝ (mt S₀ k ⬝ o.jA) := by rw [o.sum_eq_one, Matrix.one_mul]
      _ = o.jA ⬝ M := by rw [Matrix.add_mul, Matrix.mul_assoc o.jB, h1, Matrix.mul_zero, add_zero, Matrix.mul_assoc, hM]
  have hu : adj M * (gA A * M) = gA A := by
    calc adj M * (gA A * M) = adj (o.jA ⬝ M) ⬝ (gA S₀ ⬝ (o.jA ⬝ M)) := by
          rw [adj_mul, ← o.gram_AA]; simp only [Matrix.mul_assoc]
      _ = adj (mt S₀ k ⬝ o.jA) ⬝ (gA S₀ ⬝ (mt S₀ k ⬝ o.jA)) := by rw [hA]
      _ = gA A := by
          rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S₀) (mt S₀ k) o.jA,
            ← Matrix.mul_assoc (adj (mt S₀ k)) (gA S₀ ⬝ mt S₀ k) o.jA, mt_unitary, o.gram_AA]
  have key : mt S₀ k = o.jA ⬝ M ⬝ o.pA + o.jB ⬝ o.pB := by
    have e : mt S₀ k ⬝ (o.jA ⬝ o.pA + o.jB ⬝ o.pB) = mt S₀ k := by rw [o.sum_eq_one]; exact Matrix.mul_one _
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hk] at e
    exact e.symm
  exact ⟨ofMat A M hu, mt_injective S₀ (by rw [o.mt_emb, mt_ofMat, mt_one, Matrix.mul_one, key])⟩

def prodSub : Subgroup (GA D S) where
  carrier := {g | ∃ n ∈ flagN d, ∃ h, g = n * embA d o h}
  one_mem' := ⟨1, one_mem _, 1, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, hn, h, rfl⟩ ⟨n', hn', h', rfl⟩
    refine ⟨n * (embA d o h * n' * (embA d o h)⁻¹), mul_mem hn ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 n' hn' _), h * h', ?_⟩
    rw [map_mul]; group
  inv_mem' := by
    rintro _ ⟨n, hn, h, rfl⟩
    refine ⟨embA d o h⁻¹ * n⁻¹ * (embA d o h⁻¹)⁻¹, (GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 _ (inv_mem hn) _, h⁻¹, ?_⟩
    rw [map_inv]; group

theorem besGrp_le_prodSub : besGrp d o ≤ prodSub d o :=
  sup_le (fun n hn => ⟨n, hn, 1, by simp⟩) (by rintro _ ⟨h, rfl⟩; exact ⟨1, one_mem _, h, by simp⟩)

theorem besGrp_eq_inter :
    (besGrp d o : Set (GA D S)) = (jacGrp d : Set (GA D S)) ∩ {g | d.p0 ⬝ (mt S g ⬝ d.j0) ⬝ o.jB = o.jB} := by
  ext g
  constructor
  · intro hg
    obtain ⟨n, hn, h, rfl⟩ := besGrp_le_prodSub d o hg
    refine ⟨mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨o.emb (h, 1), rfl⟩), ?_⟩
    show d.p0 ⬝ (mt S (n * d.emb0 (o.emb (h, 1))) ⬝ d.j0) ⬝ o.jB = o.jB
    rw [witt_anisotropic_block_flag_mul_embedded d hn, o.emb_jB, mt_one, Matrix.mul_one]
  · rintro ⟨hg, he⟩
    obtain ⟨n, hn, k, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.1 g).1 hg
    have he' : d.p0 ⬝ (mt S (n * d.emb0 k) ⬝ d.j0) ⬝ o.jB = o.jB := he
    rw [witt_anisotropic_block_flag_mul_embedded d hn] at he'
    obtain ⟨a, ha⟩ := exists_emb_of_fix o he'
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨a, by rw [embA_apply, ha]⟩)

theorem besGrp_isClosed : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L),
    IsClosed (besGrp d o : Set (GA D S)) := by
  intro D S S₀ A L ρ d o
  rw [besGrp_eq_inter]
  haveI : T2Space (Mx D S₀.rank L.rank) := (lattice_Mx D _ _).2.2.2.1
  exact (jacGrp_closed d).inter (isClosed_eq
    ((continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)).matrix_mul continuous_const)
    continuous_const)

end GlobalTheory.BesClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_unipotent_bessel_character_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (θ : D.host.E), (∀ z, Continuous (psiBes ψ d θ z)) ∧ (∀ z, ∀ γ ∈ GQ S, psiBes ψ d θ z γ = 1) ∧ (∀ n h, psiBes ψ d θ (vecB o ζ) (embA d o h * n * (embA d o h)⁻¹) = psiBes ψ d θ (vecB o ζ) n) ∧ (∀ n h, psiFlag ψ d (d.emb0 h * n * (d.emb0 h)⁻¹) = psiFlag ψ d n) ∧ (∀ g, g ∈ besGrp d o ↔ ∃ n ∈ flagN d, ∃ h, g = n * embA d o h) ∧ ∀ ι : A.V →ₗ[D.host.E] S.V, frameMat S A ι = d.i₀ * o.iA → ∀ h, EmbRel S A ι (embA d o h) h := by
  first | exact @GlobalTheory.MixPer.charLaws | exact GlobalTheory.MixPer.charLaws | (intros; apply GlobalTheory.MixPer.charLaws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_unipotent_fourier_jacobi_group_structure : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (∀ n, n ∈ flagN d ↔ ∃ u ∈ UX D ρ, ∃ b c, n = d.levi u * (d.nB b * d.nC c)) ∧ (∀ n, n ∈ radX d ↔ ∃ b c, n = d.nB b * d.nC c) ∧ (∀ g, g ∈ stabX d ↔ ∃ n ∈ radX d, ∃ h, g = n * d.emb0 h) ∧ (∀ g, g ∈ jacGrp d ↔ ∃ n ∈ flagN d, ∃ h, g = n * d.emb0 h) ∧ (∀ n ∈ flagN d, ∀ h, d.emb0 h * n * (d.emb0 h)⁻¹ ∈ flagN d) ∧ (∀ n ∈ flagN d, ∀ n' ∈ flagN d, ∀ h h', n * d.emb0 h = n' * d.emb0 h' → n = n' ∧ h = h') ∧ ∀ u b c u' b' c', d.levi u * (d.nB b * d.nC c) = d.levi u' * (d.nB b' * d.nC c') → u = u' ∧ b = b' ∧ c = c' := by
  first | exact @GlobalTheory.MixPer.flag_jacobi_structure | exact GlobalTheory.MixPer.flag_jacobi_structure | (intros; apply GlobalTheory.MixPer.flag_jacobi_structure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockNormMinorProductDeltaAtEmbeddingPosStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockNorm_minorProductDeltaAtEmbedding_pos : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ∃ a : ℝ, 0 < a ∧ Formalism.E.fock (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.deltaAtEmb D i σ) = (a : ℂ) := by
  first | exact @GlobalTheory.FockDelta.fock_deltaAtEmb_pos | exact GlobalTheory.FockDelta.fock_deltaAtEmb_pos | (intros; apply GlobalTheory.FockDelta.fock_deltaAtEmb_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameAdjointMapReframedHermitianSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameAdjointMap_reframedHermitianSpace : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO (reS S b) T), frMapAdj (reS S b) T (frPinvGL S b * βS) βT x = frMapAdj S T βS βT (reW S T b x) := by
  first | exact @GlobalTheory.AdSpan.ReVec.FrMap.frMapAdj_reS | exact GlobalTheory.AdSpan.ReVec.FrMap.frMapAdj_reS | (intros; apply GlobalTheory.AdSpan.ReVec.FrMap.frMapAdj_reS <;> assumption)
end

