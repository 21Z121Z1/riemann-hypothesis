import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.Columns.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0448
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddLargeBaseCoreSlot
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem SecondG.sAnd_of_largeBase : ∀ (KP : GroupRetwisting.BaseP) (Q Q' R : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.LargeBaseConditionG KP Q R → GroupRetwisting.SecondG KP Q Q' →
    GroupRetwisting.SecondG KP Q (sAnd Q' R) := by
  intro KP Q Q' R hK hR hS
  refine (EvG.inter hR hS).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨S₁r, P₁r, Ar, S₂r, r1, r2, hr⟩, ⟨S₁s, P₁s, As, S₂s, s1, s2, hs⟩⟩ := H
  refine ⟨fun P g F => S₁s P g F ∪ S₁r P g F, fun P g F F₀ => P₁s P g F F₀ ∪ P₁r P g F F₀, As, S₂s, ?_, s2, ?_⟩
  · intro P g F z hz
    rcases Finset.mem_union.1 hz with h | h
    exacts [s1 _ _ _ z h, r1 _ _ _ z h]
  · intro B f T hO hH hP hA hKP hT C W V S N G c hQ hX A S₂ hS₂
    have hH' : Has₂ B (S₁s B.toPre f B.KsC) (S₂s B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f)) :=
      ⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), hH.2⟩
    obtain ⟨B', f', T', hEnl, hf', hpl, hAv, hS', C', W', V', S', N', G', c', hQ', hTw, hQ''⟩ :=
      hs B f T hO hH' (fun x hx => hP (Finset.mem_union_left _ hx)) hA hKP hT C W V S N G c hQ hX
        (fun l => A l ∪ Ar B.toPre f B.KsC B.fixedCoefficientFieldInComplex l) (fun P g Ξ => S₂ P g Ξ ∪ S₂r P g B.KsC B.fixedCoefficientFieldInComplex Ξ)
        (by
          intro P g Ξ z hz
          rcases Finset.mem_union.1 hz with h | h
          exacts [hS₂ _ _ _ z h, r2 _ _ _ _ _ z h])
    have hP' : B'.toPre = B.toPre := hEnl.1
    have cf : ∀ {α : Type} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {x : Fr P} {y : Fr P'}, P = P' → HEq x y → g P x = g P' y := by
      intro α g P P' x y h hxy
      subst h
      rw [eq_of_heq hxy]
    have hk : B'.KsC = B.KsC := hEnl.KsC_eq
    have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := hEnl.fixedCoefficientField_eq
    have hRc : R K ⟨B', C', W', V', S', N', G'⟩ f' T' c' :=
      hr B' f' T' (hP' ▸ hO)
        ⟨by rw [hk, hl, cf S₁r hP' hf']; exact fun z hz => hH.1 z (Finset.mem_union_right _ hz),
          by rw [hk, hl]; exact fun z hz => hS' z (Finset.mem_union_right _ hz)⟩
        (by rw [hk, hl, cf P₁r hP' hf', hpl]; exact fun x hx => hP (Finset.mem_union_right _ hx))
        (by
          rw [hk, hl, cf Ar hP' hf']
          exact fun w v hv h => hAv w v hv (Finset.mem_union_right _ h))
        (hK.enl B B' f f' hEnl hf' hKP) C' W' V' S' N' G' c' hQ'
    exact ⟨B', f', T', hEnl, hf', hpl, fun w v hv h => hAv w v hv (Finset.mem_union_left _ h),
      fun z hz => hS' z (Finset.mem_union_left _ hz), C', W', V', S', N', G', c', hQ', hTw, hQ'', hRc⟩

end GlobalTheory.Mem.Top.GroupRetwisting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBasePointChartMulTwist
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

theorem carries_mul_self {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {g h : GL (Fin N) (TensorProduct F E (Formalism.L2.Herm.Af F))} {L : Submodule (𝓞 E) (Fin N → E)}
    (hg : Formalism.L2.Herm.Carries g L L) (hh : Formalism.L2.Herm.Carries h L L) : Formalism.L2.Herm.Carries (g * h) L L := by
  intro x
  rw [hg x, hh, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]

set_option maxHeartbeats 1000000 in

theorem admissibleBasePoint_chart_mul_twist : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (Lb0 : Ch0 → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U0 : Ch0 → Subgroup (GA B (B.R.N i))) (chi0 : ∀ β, U0 β →* ℂˣ) (y0 : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)) (st0 : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k0 : Ch0 → GA B (B.R.N i)), I.Reads u I.mu0 i chOf0 Lb0 U0 chi0 y0 st0 k0 → ∀ (g : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → Ch0) (t : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), (∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (t β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) → (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (t β) = 1) → (a = I.mu0 → ∀ β, t β = 1) → GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i (fun β => k0 (g β) * t β) := by
  intro B X I hI u a i Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 hR g t hstd hoff h0
  refine ⟨fun β => ?_, fun β v hT hQ hd => ?_, fun β P r j hr => ?_⟩
  · obtain ⟨p, hp, hN⟩ := hR.k_std (g β)
    obtain ⟨q, hq, hN'⟩ := hstd β
    have h1 := hp.lat
    have h2 := hq.lat
    rw [hN] at h1
    rw [hN'] at h2
    refine ⟨p, ⟨mul_mem hp.uni hq.uni, ?_, fun P => ?_, fun w => ?_, fun P => ?_⟩, hN⟩
    · rw [hN]
      exact carries_mul_self h1 h2
    · exact absurd P.2 (Finset.notMem_empty _)
    · exact absurd w.2 (Finset.notMem_empty _)
    · exact absurd P.2 (Finset.notMem_empty _)
  · have hq0 : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty _
    have hk : bc (prV (E := B.host.E) v) (k0 (g β)) = 1 :=
      hR.k_off (g β) v hT (by rintro ⟨P, hP, -⟩; rw [hq0] at hP; simp at hP) (Or.inl rfl)
    have ht : bc (prV (E := B.host.E) v) (t β) = 1 := by
      rcases hd with rfl | hd
      · rw [h0 rfl β, map_one]
      · exact hoff β v (Or.inr hd)
    have hm := map_mul (bc (prV (E := B.host.E) v)) (k0 (g β)) (t β)
    rw [hk, ht, one_mul] at hm
    exact hm
  · have hv : (B.T u : 𝓞 B.host.F) ∈ (P.1.under (𝓞 B.host.F)).asIdeal := by
      have := T_mem_vT (GlobalTheory.BasePrimes.primes_ok B X).1 u P
      rw [HeightOneSpectrum.under, Ideal.mem_comap, map_natCast]
      exact this
    have ht := hoff β _ (Or.inl hv)
    have ht' := (map_inv (bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F)))) (t β)).trans (by rw [ht, inv_one])
    have hent : ∀ r l, adAt B.host.F P.1 (((t β)⁻¹ : GA B (B.R.N i)).1 r l) = if r = l then 1 else 0 := by
      intro r l
      have e := congrArg (fun g => g.1 r l) ht'
      simp only [bc, Units.coe_map, Units.val_one, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at e
      split_ifs with h
      · subst h
        exact FullDt.adAt_eq_one_of_prV P.1 (by simpa using e)
      · exact TilX.adAt_eq_zero_of_prV P.1 _ (by simpa [Matrix.one_apply_ne h] using e)
    have key : adAt B.host.F P.1 (((k0 (g β) * t β)⁻¹ : GA B (B.R.N i)).1 r j) =
        adAt B.host.F P.1 (((k0 (g β))⁻¹ : GA B (B.R.N i)).1 r j) := by
      rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply, map_sum]
      simp only [map_mul, hent, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [key]
    exact hR.k_T (g β) P r j hr

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepWeightArithmetic
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

namespace GlobalTheory.IntegralityCompare

theorem weight_arith_step : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (μ : I.ι) (i : ℕ), i < B.R.m →
    ∃ k : (I.rec7 l Z).what₂.Tau → ℕ,
      (∀ τ, (k τ : ℤ) = shiftOf (lamTG (I.fm l u μ) i) τ + ((I.rec7 l Z).chTw u μ).sSharp i τ) ∧
      ∀ τ r, nuT (I.rec7 l Z) u i τ r = ((I.fm l u μ).lam i τ).natW r + k τ := by
  intro B X I hOk hPins l Z u μ i hi
  obtain ⟨n, h1, h2, -, -⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ (I.fm l u μ) i hi
  refine ⟨n, fun τ => ?_, fun τ r => ?_⟩
  · rw [← h2 τ]; rfl
  · rw [← h1 τ r]
    unfold lamTG
    rw [natW_shW]
    rfl

end GlobalTheory.IntegralityCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelTwistTrivialLocalMove
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChTwRead

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def noFr (p : DecoF E n ST SG Q) : DecoF E n ST SG ∅ :=
  ⟨(p.deco, fun P => absurd P.2 (Finset.notMem_empty _)), fun P => absurd P.2 (Finset.notMem_empty _)⟩

theorem isPtOf_iff (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) :
    IsPtOf hc g p ↔ (g ∈ UAd hc n ∧ p.deco.1 = decoRaw ST SG g) ∧
      ∀ (P : Q) (i j : Fin n), adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        algebraMap E _ (p.fr P (Pi.single j 1) i) := by
  have key := PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ g (noFr p) rfl
  constructor
  · intro h
    exact ⟨key.1 ⟨h.uni, h.lat, h.f, h.be, fun P => absurd P.2 (Finset.notMem_empty _)⟩, h.fr⟩
  · rintro ⟨h, h'⟩
    have h2 := key.2 h
    exact ⟨h2.uni, h2.lat, h2.f, h2.be, h'⟩

theorem adAt_congr_prV (P : HeightOneSpectrum (𝓞 E)) {z z' : AfE F E}
    (h : prV (E := E) (P.under (𝓞 F)) z = prV (E := E) (P.under (𝓞 F)) z') : adAt F P z = adAt F P z' := by
  have h0 := TilX.adAt_eq_zero_of_prV P (z - z') (by rw [map_sub, h, sub_self])
  rwa [map_sub, sub_eq_zero] at h0

theorem exists_pt_of_agree {g₁ g' : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h₁ : IsPtOf hc g₁ p)
    (hg' : g' ∈ UAd hc n)
    (hv : ∀ P ∈ Q, bc (prV (E := E) (P.under (𝓞 F))) g' = bc (prV (E := E) (P.under (𝓞 F))) g₁) :
    ∃ q : DecoF E n ST SG Q, IsPtOf hc g' q := by
  obtain ⟨⟨-, hd1⟩, -⟩ := (isPtOf_iff hc g₁ p).1 h₁
  have hloc : ∀ P ∈ Q, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat g' (stdLat E n)) =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal p.deco.1.N := by
    intro P hP
    rw [hd1]
    exact updn_mem_loc (v := P.under (𝓞 F)) (P := P) rfl (hv P hP)
  refine ⟨⟨(⟨decoRaw ST SG g', decorated_lattice_exists hc n ST SG g' hg'⟩, p.fr), fun P x => ?_⟩, ?_⟩
  · show p.fr P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat g' (stdLat E n)) ↔ _
    rw [hloc P.1 P.2]
    exact p.2 P x
  · refine (isPtOf_iff hc g' _).2 ⟨⟨hg', rfl⟩, fun P i j => ?_⟩
    show _ = algebraMap E _ (p.fr P (Pi.single j 1) i)
    rw [← h₁.fr P i j]
    apply adAt_congr_prV
    exact congrArg (fun g => g.1 i j) (hv P.1 P.2)

theorem isPtOf_mul {g g₁ s : GL (Fin n) (AfE F E)} {p q : DecoF E n ST SG Q} (h : GLG E n SG)
    (hq : q.deco.1 = p.deco.1.act 1 h) (hg : IsPtOf hc g p) (hg₁ : IsPtOf hc g₁ p) (hs : IsPtOf hc (g₁ * s) q) :
    IsPtOf hc (g * s) q := by
  obtain ⟨⟨hgu, hdg⟩, hfg⟩ := (isPtOf_iff hc g p).1 hg
  obtain ⟨⟨hu1, hd1⟩, hf1⟩ := (isPtOf_iff hc g₁ p).1 hg₁
  obtain ⟨⟨hsu, hds⟩, hfs⟩ := (isPtOf_iff hc (g₁ * s) q).1 hs
  have hsU : s ∈ UAd hc n := by
    have e : s = g₁⁻¹ * (g₁ * s) := by group
    rw [e]
    exact mul_mem (inv_mem hu1) hsu
  obtain ⟨hJ, -⟩ := mem_congruence_of_action hc ST SG hsu hu1 h (by rw [← hds, hq, hd1])
  have hK := mem_principal_of_same_decoration hc n ST SG hu1 hgu (hd1.symm.trans hdg)
  have hc' := K1_conj hc n ST SG ⟨_, hJ⟩ (a := ⟨g₁⁻¹ * g, principal_le_adelic_unitary hc n ST SG hK⟩)
    (Subgroup.mem_subgroupOf.2 hK)
  rw [Subgroup.mem_subgroupOf] at hc'
  have e : g * s = (g₁ * s) * ((((g₁ * s)⁻¹ * g₁) * (g₁⁻¹ * g)) * ((g₁ * s)⁻¹ * g₁)⁻¹) := by group
  have hdr : decoRaw ST SG (g * s) = decoRaw ST SG (g₁ * s) := by
    rw [e]
    exact decorated_lattice_mul_principal hc n ST SG _ hc'
  refine (isPtOf_iff hc (g * s) q).2 ⟨⟨mul_mem hgu hsU, hds.trans hdr.symm⟩, fun P i j => ?_⟩
  rw [← hfs P i j, Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_mul, hfg P i l, hf1 P i l]

end GlobalTheory.Mem.Col2.ChTwRead

namespace GlobalTheory.Mem.Col2.TC.ChTw

theorem locMv_of_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m → ∀ {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) (Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U : Ch → Subgroup (GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a i).Cl → GA B (B.R.N i)) (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k : Ch → GA B (B.R.N i)), I.Reads u a i chOf Lb U chi y st k → ∀ (c : (I.stp u a i).Cl) (x : GA B (B.R.N i)), x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) → (∀ v, I.UnderQ a v → bc (prV (E := B.host.E) v) x = 1) → x ∈ U (chOf c) → ∃ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((k (chOf c))⁻¹ * x * k (chOf c)) κ := by
  intro B X I hI _ u a i _ Ch chOf Lb U chi y st k hR c x hx hx1 hxU
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  obtain ⟨pk, hpk, -⟩ := hR.k_std (chOf c)
  have hk : k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := hpk.uni
  have hg' : y c * x * k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := by
    have e : y c * x * k (chOf c) = y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) := by group
    rw [e]
    exact mul_mem hp.uni (mul_mem (mul_mem (inv_mem hk) hx) hk)
  have hv : ∀ P ∈ I.Q a, bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) (y c * x * k (chOf c)) =
      bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) (y c * k (chOf c)) := by
    intro P hP
    have h1 := hx1 (P.under (𝓞 B.host.F)) ⟨P, hP, rfl⟩
    simp only [map_mul, h1, mul_one]
  obtain ⟨q, hq⟩ := ChTwRead.exists_pt_of_agree B.sp.cm hp hg' hv
  obtain ⟨κ, hκ1, hκq, hκc⟩ := (hR.lev c x q hq).1 hxU
  refine ⟨κ, hκ1, hκc, fun g hg => ?_⟩
  have e : y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) = y c * x * k (chOf c) := by group
  have hγ : κ.1 = 1 := by
    have h1 : toGLm B.fields.E (B.R.N i) κ.1.1 = toGLm B.fields.E (B.R.N i) 1 := by
      rw [map_one]
      exact hκ1
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective h1)
  · refine ChTwRead.isPtOf_mul B.sp.cm κ.2.1.1 ?_ hg hp (by rw [e, hκq]; exact hq)
    show ((κ.1, (κ.2.1 : GLG B.fields.E (B.R.N i) (B.primes X).vGs)) • ((I.stp u a i).rep c).1.1.deco).1 = _
    rw [hγ]
    rfl
end GlobalTheory.Mem.Col2.TC.ChTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffFieldRootsOfUnityTypePrimesHermitianStages
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Cls

theorem coeffField_rootsOfUnity_typePrimes_hermitianStages : ∀ X : Stages, GlobalTheory.Core.Cls.RootsG X.toD7 := by
  intro X i
  have hp : Nat.Prime (X.B.host.g i) := X.B.host.g_prime i
  obtain ⟨z, -, hz⟩ := X.B.roots_Ks (X.B.host.g i * (X.B.host.g i - 1)) (by fin_cases i <;> simp)
  have hne : X.B.host.g i * (X.B.host.g i - 1) ≠ 0 :=
    mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot z (X.B.host.g i * (X.B.host.g i - 1)) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := X.B.embLL) ?_ X.B.embLL.injective
    rw [hz]
    exact_mod_cast Complex.isPrimitiveRoot_exp _ hne
  have hpos : 0 < X.B.host.g i * (X.B.host.g i - 1) := Nat.pos_of_ne_zero hne
  exact ⟨⟨z ^ (X.B.host.g i - 1), hprim.pow hpos (mul_comm _ _)⟩, ⟨z ^ X.B.host.g i, hprim.pow hpos rfl⟩⟩

end GlobalTheory.Core.Cls
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientFieldFormValueMemPolynomialModelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientField_form_value_mem_polynomialModel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (x : (((I.tw l l0 Z).fm u μ).lat (i + 1)).V) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)), ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = ((I.tw l l0 Z).fm u μ).emb (i + 1) x c' := by
  first | exact @GlobalTheory.Mem.KerVal.fm_succ_mem_valQ | exact GlobalTheory.Mem.KerVal.fm_succ_mem_valQ | (intros; apply GlobalTheory.Mem.KerVal.fm_succ_mem_valQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexValueDetShiftMulRatSpan
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerValRat

theorem lamTG_add_sSharp {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : Fin (D.R.N i)) :
    (lamTG M i τ).w r + (D.chTw u μ).sSharp i τ = (nuT D u i τ r : ℤ) := by
  obtain ⟨a, ha⟩ := D.R.t_odd
  have hc : ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) = (i : ℝ) * ((a : ℝ) + 1) := by
    rw [ha, show i * (2 * a + 1 + 1) = 2 * (i * (a + 1)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    push_cast; ring
  have ht : (D.R.t : ℝ) = 2 * a + 1 := by rw [ha]; push_cast; ring
  have h1 := congrArg (Rat.cast : ℚ → ℝ) (M.lam_eq i hi.le τ r)
  have h2 := congrArg (Rat.cast : ℚ → ℝ) ((D.chTw u μ).sSharp_eq i hi τ)
  have h3 := GlobalTheory.PdvKm.nuT_real u i hi τ r
  have he := D.hcW_e u τ
  suffices key : (((lamTG M i τ).w r : ℤ) : ℝ) + (((D.chTw u μ).sSharp i τ : ℤ) : ℝ) = ((nuT D u i τ r : ℕ) : ℝ) by
    exact_mod_cast key
  rw [h3]
  have e0 : (lamTG M i τ).w r = (M.lam i τ).w r - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ) := rfl
  have hl : (((lamTG M i τ).w r : ℤ) : ℝ) = ((((M.lam i τ).w r : ℤ) : ℚ) : ℝ) - (i : ℝ) * ((a : ℝ) + 1) := by
    rw [e0, Int.cast_sub, Int.cast_natCast, hc, Rat.cast_intCast]
  have hs : (((D.chTw u μ).sSharp i τ : ℤ) : ℝ) = ((((D.chTw u μ).sSharp i τ : ℤ) : ℚ) : ℝ) := by rw [Rat.cast_intCast]
  rw [hl, hs, h1, h2]
  have hw : DV.wSz D (i + 1) τ = (((D.hcW u τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
    unfold DV.wSz
    rw [dif_pos ⟨by omega, by omega⟩, he]
    rfl
  unfold DV.nuRow
  rw [hw]
  unfold DV.srcPar sExp' Ranks.N
  by_cases hk : r.1 < D.R.k
  · rw [dif_pos hk, dif_pos hk]
    unfold hcToWeightQ rhoVec
    push_cast
    rw [ht]
    ring
  · rw [dif_neg hk, dif_neg hk]
    have hr := r.2
    unfold Ranks.N at hr
    have hb : (r.1 - D.R.k) / (D.R.t + 1) < i := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      exact Nat.sub_lt_left_of_lt_add (by omega) hr
    have hbm : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by omega
    rw [dif_pos hbm]
    have hdm := Nat.div_add_mod (r.1 - D.R.k) (D.R.t + 1)
    have hr' : (r.1 : ℝ) = D.R.k + (D.R.t + 1) * (((r.1 - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) + (((r.1 - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      have : r.1 = D.R.k + ((D.R.t + 1) * ((r.1 - D.R.k) / (D.R.t + 1)) + (r.1 - D.R.k) % (D.R.t + 1)) := by omega
      conv_lhs => rw [this]
      push_cast; ring
    unfold wG
    push_cast
    rw [hr', ht]
    ring

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

open GlobalTheory.PdvKm in
theorem detShift_lamTG {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    (lamTG M i τ).detShift = (nuT D u i τ (lastI D i) : ℤ) - (D.chTw u μ).sSharp i τ := by
  have h := lamTG_add_sSharp M μ i hi τ (lastI D i)
  unfold DomWeight.detShift
  rw [dif_pos (N_pos D i)]
  show (lamTG M i τ).w (lastI D i) = _
  omega

open GlobalTheory.PdvKm in
theorem natW_lamTG {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {P : PeriodMap D.R C} (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)
    (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : Fin (D.R.N i)) :
    (M.lam i τ).natW r = nuT D u i τ r - nuT D u i τ (lastI D i) := by
  have h0 : (M.lam i τ).natW r = (lamTG M i τ).natW r := by
    show _ = (Formalism.L2.Forms.shW (M.lam i τ) _).natW r
    rw [Formalism.L2.Forms.natW_shW]
  rw [h0]
  have h1 := lamTG_add_sSharp M D.what₂.mu0 i hi τ r
  have h2 := detShift_lamTG M D.what₂.mu0 i hi τ
  have hle : nuT D u i τ (lastI D i) ≤ nuT D u i τ r :=
    antitone_kernelChain_nuT D u i τ hi (show r ≤ lastI D i by rw [Fin.le_def]; simp only [lastI]; omega)
  unfold DomWeight.natW
  rw [h2]
  omega

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

open GlobalTheory.PdvKm in
theorem evC_ratSpan_gen {D : D7} (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup)
    {A : ColumnsAtT D.R (D.chTw u μ)} {P : PeriodMap D.R (D.chTw u μ)}
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) (D.chTw u μ) A P)
    (i : ℕ) (hi : i < D.R.m) (eY : (D.chTw u μ).Y i ≃ Fr D i hi.le)
    (hfrm : ∀ y, (O u μ).frm i y = (eY y).1) (v : ValQ O u μ i) :
    ∃ Q ∈ Formalism.L2.Forms.RatSpan D (M.lam i), ∀ z, evC O u μ i v z =
      fnOf (gramC (gramN D i hi.le) (embT D)) (shiftOf (lamTG M i)) 1 Q (eY z) := by
  have hne : ∀ (z : (D.chTw u μ).Y i) τ, ((eY z).1 τ).det ≠ 0 := fun z τ => by
    rw [← hfrm z, ← (O u μ).frm_de i hi.le z τ]; exact (D.chTw u μ).de_ne i z τ
  have hev : ∀ z, evC O u μ i v z = (∏ τ, (((eY z).1 τ).det) ^ (-(twB D u μ i τ))) *
      MvPolynomial.eval₂ D.what₂.embLL (fun k => (eY z).1 k.1 k.2.1 k.2.2)
        (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL) := by
    intro z
    rw [evC_sec]
    show (∏ τ, ((D.chTw u μ).de i z τ) ^ (-(twB D u μ i τ))) *
      GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) ((O u μ).frm i z) = _
    simp only [(O u μ).frm_de i hi.le z, hfrm z, evFr_map]
  have hfn : ∀ (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ) z,
      fnOf (gramC (gramN D i hi.le) (embT D)) (shiftOf (lamTG M i)) 1 Q (eY z) =
        (∏ τ, ((eY z).1 τ).det ^ (lamTG M i τ).detShift) * MvPolynomial.eval (fun x => (eY z).1 x.1 x.2.1 x.2.2) Q := by
    intro Q z
    show (∏ τ, ((1 : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) τ * (eY z).1 τ).det ^ _) *
      MvPolynomial.eval (fun x => ((1 : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) x.1 * (eY z).1 x.1) x.2.1 x.2.2) Q = _
    simp only [Pi.one_apply, one_mul]
    rfl

  haveI hLL : Infinite D.what₂.LL := Infinite.of_injective (fun n : ℕ => (n : D.what₂.LL)) (fun a b h => by
    have := congrArg D.what₂.embLL h; simp only [map_natCast] at this; exact_mod_cast this)
  have hmem : (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL) ∈ polV D u i := (secC O u μ i v).2
  rcases i with _ | j
  · have h0 : 0 < D.R.m := hi
    have hk : ∀ τ r, nuT D u 0 τ (lastI D 0) ≤ nuT D u 0 τ r := fun τ r =>
      antitone_kernelChain_nuT D u 0 τ h0 (show r ≤ lastI D 0 by rw [Fin.le_def]; simp only [lastI]; omega)
    obtain ⟨P0, hP0, hQe⟩ := frameWeightPolyDivByDet_proof D.what₂.LL D.what₂.Tau (D.R.N 0) (nuT D u 0) (fun τ => nuT D u 0 τ (lastI D 0)) hk _ hmem
    refine ⟨MvPolynomial.map D.what₂.embLL P0, GlobalTheory.LevelHecke.map_mem_ratSpan (M.lam 0) ?_, fun z => ?_⟩
    · rw [VV_eq_WtPol]
      have e : (fun τ r => (M.lam 0 τ).natW r) = fun τ r => nuT D u 0 τ r - nuT D u 0 τ (lastI D 0) :=
        funext fun τ => funext fun r => natW_lamTG M 0 h0 τ r
      rw [e]; exact hP0
    · have hd : ∀ τ, MvPolynomial.eval₂ D.what₂.embLL (fun k : GL3Theta.FrV D (D.R.N 0) => (eY z).1 k.1 k.2.1 k.2.2)
          (frDet D.what₂.LL (D.R.N 0) τ) = ((eY z).1 τ).det := by
        intro τ
        rw [← MvPolynomial.eval_map, Formalism.L2.Ker.map_frDet, Formalism.L2.Ker.eval_frDet]
        rfl
      rw [hev, hfn, hQe, MvPolynomial.eval_map, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod]
      simp only [MvPolynomial.eval₂_pow, hd]
      have hs : ∀ τ, (lamTG M 0 τ).detShift = ((nuT D u 0 τ (lastI D 0) : ℕ) : ℤ) - twB D u μ 0 τ :=
        fun τ => detShift_lamTG M μ 0 h0 τ
      simp only [hs]
      rw [prod_zpow_split _ (hne z) _ (fun τ => nuT D u 0 τ (lastI D 0))]
      ring
  · have hj : j < D.R.m := by omega
    refine ⟨MvPolynomial.map D.what₂.embLL (secC O u μ (j + 1) v : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) D.what₂.LL),
      GlobalTheory.LevelHecke.map_mem_ratSpan (M.lam (j + 1)) ?_, fun z => ?_⟩
    · rw [VV_eq_WtPol]
      have e : (fun τ r => (M.lam (j + 1) τ).natW r) = extNu (D.R.N (j + 1)) (nuT D u j) := by
        funext τ r
        rw [natW_lamTG M (j + 1) hi τ r, ← natW_succ (antitone_kernelChain_nuT D) u j hj τ r]
        have h1 := clause1 (antitone_kernelChain_nuT D) u (j + 1) hi τ r
        have h2 : nn D u (j + 1) τ = nuT D u (j + 1) τ (lastI D (j + 1)) := by unfold nn; rw [if_pos hi]
        omega
      rw [e]; exact hmem
    · rw [hev, hfn, MvPolynomial.eval_map]
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      congr 1
      rw [detShift_lamTG M μ (j + 1) hi τ]
      have h1 := last_real u μ j hi τ
      show -((D.chTw u μ).sDiv j τ) = _
      have h2 : ((nuT D u (j + 1) τ (lastI D (j + 1)) : ℕ) : ℤ) = (D.chTw u μ).sSharp (j + 1) τ - (D.chTw u μ).sDiv j τ := by
        exact_mod_cast h1
      omega

end GlobalTheory.KerValRat

namespace GlobalTheory.KerValRat

theorem evC_ratSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ v : ValQ O u μ i, ∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, evC O u μ i v z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z) := by
  intro B X I hOk hPins l Z Y O hQ hS u μ i hi eY hId v
  exact evC_ratSpan_gen O u μ (I.fm l u μ) i hi eY (fun y => (hS.frm u μ i y).trans (hId y).symm) v

end GlobalTheory.KerValRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphicSideEmptyLocalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_automorphic_side_empty_local : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), IsEmpty D.nd.Loc → ∀ T : GlobalTheory.RowTie.WDTie D.nd D.naut, ∃ (C : NBC D.naut) (A : AUSide (setBC D C)), AUTrue hL (setBC D C) T A := by
  first | exact @GlobalTheory.AutQuot.exists_nbc_auSide | exact GlobalTheory.AutQuot.exists_nbc_auSide | (intros; apply GlobalTheory.AutQuot.exists_nbc_auSide <;> assumption)
end

