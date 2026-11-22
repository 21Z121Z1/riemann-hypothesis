import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.LvProj

open GlobalTheory.LvT.Pts
open Formalism.HermitianLatticesTheory (localization₂ dual)

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {M A : Submodule (𝓞 E) (Fin n → E)} {P : HeightOneSpectrum (𝓞 E)}

theorem redL_osmul (r : 𝓞 E) {x : Fin n → E} (hx : x ∈ localization₂ P.asIdeal M) :
    redL M P (r • x) = (Ideal.Quotient.mk P.asIdeal r : Res P) • redL M P x := by
  obtain ⟨s, hs, hx⟩ := (mem_locP P M _).1 hx
  refine redL_eq hs (by rw [smul_comm]; exact M.smul_mem _ hx) ?_
  rw [smul_comm, redL_spec hs hx, mk_smul_mk]
  congr 1
  exact Subtype.ext (smul_comm _ _ _)

omit [StarRing E] in
theorem redL_zero : redL M P 0 = 0 := redL_coe (M := M) (P := P) 0

def proj (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) : A →+ TDat.Red M P where
  toFun z := redL M P z.1
  map_zero' := redL_zero
  map_add' x y := redL_add (h ▸ le_locP P A x.2) (h ▸ le_locP P A y.2)

theorem proj_mk (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) (z : A) (hz : z.1 ∈ M) :
    proj h z = Submodule.Quotient.mk ⟨z.1, hz⟩ := redL_coe (M := M) (P := P) ⟨z.1, hz⟩

theorem proj_smul (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) (a : 𝓞 E) (z : A) :
    proj h (a • z) = (Ideal.Quotient.mk P.asIdeal a : Res P) • proj h z :=
  redL_osmul a (h ▸ le_locP P A z.2)

theorem proj_surj (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) : Function.Surjective (proj h) := by
  intro y
  obtain ⟨x, hx, rfl⟩ := redL_surj y
  have hx' : x ∈ localization₂ P.asIdeal M := le_locP P M hx
  obtain ⟨s, hs, hsx⟩ := (mem_locP P A x).1 (h ▸ hx')
  obtain ⟨t, p, hp, e⟩ := P.isMaximal.exists_inv hs
  refine ⟨⟨(t * s) • x, by rw [mul_smul]; exact A.smul_mem _ hsx⟩, ?_⟩
  show redL M P ((t * s) • x) = _
  have e2 : (Ideal.Quotient.mk P.asIdeal (t * s) : Res P) = 1 := by
    rw [← map_one (Ideal.Quotient.mk P.asIdeal), ← e, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hp, add_zero]
  rw [redL_osmul _ hx', e2, one_smul]

theorem proj_ker (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) {J : Ideal (𝓞 E)} (hJ : J = P.asIdeal) (z : A) :
    proj h z = 0 ↔ z.1 ∈ J • A := by
  subst hJ
  show redL M P z.1 = 0 ↔ _
  constructor
  · intro h0
    obtain ⟨s, hs, hx⟩ := (mem_locP P M _).1 (h ▸ le_locP P A z.2)
    have h1 := redL_spec hs hx
    rw [h0, smul_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h1
    have h2 := Submodule.mem_map_of_mem (f := M.subtype) h1
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at h2
    have key : P.asIdeal • M ≤ localization₂ P.asIdeal (P.asIdeal • A) := by
      rw [Submodule.smul_le]
      intro r hr y hy
      obtain ⟨t, ht, hty⟩ := (mem_locP P A y).1 (h ▸ le_locP P M hy)
      exact (mem_locP P _ _).2 ⟨t, ht, by rw [smul_comm]; exact Submodule.smul_mem_smul hr hty⟩
    obtain ⟨t, ht, h3⟩ := (mem_locP P _ _).1 (key h2)
    refine mem_smul_of_loc z.2 (s := t * s) (fun hm => (P.isPrime.mem_or_mem hm).elim ht hs) ?_
    rw [mul_smul]
    exact h3
  · intro hz
    have key : ∀ y ∈ P.asIdeal • A, y ∈ A ∧ redL M P y = 0 := by
      intro y hy
      refine Submodule.smul_induction_on hy (fun r hr w hw => ⟨A.smul_mem _ hw, ?_⟩) (fun y w hy hw => ⟨A.add_mem hy.1 hw.1, ?_⟩)
      · rw [redL_osmul r (h ▸ le_locP P A hw), Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_smul]
      · rw [redL_add (h ▸ le_locP P A hy.1) (h ▸ le_locP P A hw.1), hy.2, hw.2, add_zero]
    exact (key _ hz).2

end Red

section Dec

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem dualL_one (σ : E →+* E) (hσ : ∀ x, σ x = star x) {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    (L : Submodule (𝓞 E) (Fin n → E)) : Formalism.L2.Forms.dualL σ J L = dual (hStd E n) L := by
  subst hJ
  have : Formalism.BasicNotions.dualSet σ (1 : Matrix (Fin n) (Fin n) E) L = (dual (hStd E n) L : Set (Fin n → E)) := by
    ext y
    rw [SetLike.mem_coe, Formalism.L2.Col.mem_dual]
    refine forall₂_congr fun x _ => ?_
    have e : Formalism.UG.hform σ (1 : Matrix (Fin n) (Fin n) E) x y = hStd E n x y := by
      show _ = ∑ i, star (x i) * y i
      unfold Formalism.UG.hform
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.one_apply, hσ]
    rw [e, Submodule.mem_one]
    rfl
  unfold Formalism.L2.Forms.dualL
  rw [this, Submodule.span_eq]

variable {d : Deco E n ST SG} {a : 𝓞 E}

theorem localization_L_eq_localization_dnN (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) : localization₂ P.1.asIdeal d.L = localization₂ P.1.asIdeal (d.dnN P) := by
  rw [(hd.dnN_spec P hne).2.2.2]
  apply le_antisymm
  · refine localization_le_of_smul_mem (one_notMem P.1) fun x hx => ?_
    rw [one_smul]
    obtain ⟨h1, h2⟩ := (hd.mem_L x).1 hx
    exact (hd.mem_kerAt P x).2 ⟨h1, h2 P⟩
  · refine localization_le_of_le_localization _ fun x hx => ?_
    obtain ⟨h1, h2⟩ := (hd.mem_kerAt P x).1 hx
    exact (hd.mem_locP_L P x).2 ⟨le_locP _ _ h1, h2⟩

theorem sup_le_locP (hd : d.Ok) (ha : SepElt ST a) (P : ST) : d.L ⊔ P.1.asIdeal • d.Lsh ≤ localization₂ P.1.asIdeal d.L := by
  refine sup_le (le_locP _ _) ?_
  rw [Submodule.smul_le]
  intro r hr y hy
  have hy' := hd.Lsh_le_at ha P hy
  exact (hd.mem_locP_L P _).2 ⟨Submodule.smul_mem _ _ hy', by
    rw [hd.f_smul P r y hy', Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]⟩

theorem localization_Lsh_eq_localization_N (hd : d.Ok) (ha : SepElt ST a) (P : ST) {A : Submodule (𝓞 E) (Fin n → E)} (hA : A = d.Lsh) :
    localization₂ P.1.asIdeal A = localization₂ P.1.asIdeal d.N := hA ▸ hd.locP_Lsh ha P

theorem localization_sup_eq_localization_dnN (hd : d.Ok) (ha : SepElt ST a) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) {A : Submodule (𝓞 E) (Fin n → E)}
    (hA : A = d.L ⊔ P.1.asIdeal • d.Lsh) : localization₂ P.1.asIdeal A = localization₂ P.1.asIdeal (d.dnN P) := by
  subst hA
  rw [← localization_L_eq_localization_dnN hd P hne]
  exact le_antisymm (localization_le_of_le_localization _ (sup_le_locP hd ha P))
    (localization_le_of_smul_mem (one_notMem P.1) fun x hx => by rw [one_smul]; exact Submodule.mem_sup_left hx)

theorem f_eq_zero_iff (hd : d.Ok) (ha : SepElt ST a) (P : ST) {z : Fin n → E} (hz : z ∈ d.Lsh) :
    d.f P z = 0 ↔ z ∈ d.L ⊔ P.1.asIdeal • d.Lsh := by
  constructor
  · intro h0
    obtain ⟨s, hs, hsz⟩ := (mem_locP _ _ _).1 ((hd.mem_locP_L P z).2 ⟨hd.Lsh_le_at ha P hz, h0⟩)
    obtain ⟨t, p, hp, e⟩ := P.1.isMaximal.exists_inv hs
    have : z = t • (s • z) + p • z := by rw [← mul_smul, ← add_smul, e, one_smul]
    rw [this]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ t hsz) (Submodule.smul_mem_smul hp hz)
  · intro h
    exact ((hd.mem_locP_L P z).1 (sup_le_locP hd ha P h)).2

theorem reductionModPrime_levelPrime_smul_eq (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal) {z e : Fin n → E}
    (hz : z ∈ d.at P.1) (hfz : d.f P z = 1) (he : e ∈ d.N) (hfe : d.f P e = 1) (t : d.dnN P) (ht : t.1 = q • e) :
    redL (d.dnN P) P.1 (q • z) = Submodule.Quotient.mk t := by
  have he' : e ∈ d.at P.1 := le_locP _ _ he
  have hn : (-1 : 𝓞 E) • e ∈ d.at P.1 := Submodule.smul_mem _ _ he'
  have m : z + (-1 : 𝓞 E) • e ∈ localization₂ P.1.asIdeal (d.dnN P) := by
    rw [← localization_L_eq_localization_dnN hd P hne]
    refine (hd.mem_locP_L P _).2 ⟨Submodule.add_mem _ hz hn, ?_⟩
    rw [hd.f_add P _ hz _ hn, hd.f_smul P _ _ he', hfz, hfe, map_neg, map_one]
    ring
  have e1 : q • z = q • (z + (-1 : 𝓞 E) • e) + t.1 := by
    rw [ht, neg_one_smul, ← smul_add, neg_add_cancel_right]
  rw [e1, redL_add (Submodule.smul_mem _ _ m) (le_locP _ _ t.2), redL_osmul _ m,
    Ideal.Quotient.eq_zero_iff_mem.2 hq, zero_smul, zero_add, redL_coe]

end Dec

section TD

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem fv_mk (hl : A.Laws T) (P : ST) (c : S.Cl) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  have h0 := hl.fv_ne P c
  unfold TDat.fv at h0 ⊢
  split_ifs at h0 ⊢ with h1
  · exact h1.choose_spec x
  · exact absurd rfl h0

theorem te_mk (hl : A.Laws T) (P : ST) (c : S.Cl) :
    ∃ t : A.dnN c.1 (S.rep c) P, (∃ e ∈ A.N c.1 (S.rep c), A.f c.1 (S.rep c) P e = 1 ∧ (t : Fin n → E) = (T : 𝓞 E) • e) ∧
      Submodule.Quotient.mk t = A.te T P c := by
  have h0 := hl.te_ne P c
  unfold TDat.te at h0 ⊢
  split_ifs at h0 ⊢ with h1
  · exact ⟨h1.choose, h1.choose_spec, rfl⟩
  · exact absurd rfl h0

end TD

end GlobalTheory.Mem.Col2.LvProj

end

open GlobalTheory.Mem.Col2.LvProj GlobalTheory.LvT.Pts in
set_option maxHeartbeats 1600000 in

theorem GlobalTheory.Mem.Col2.TC.exists_level_projections : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∃ (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.IdL l Z u a i hi L := by
  intro B X I hI hP l Z u a i hi
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨hg, -, hc⟩ := hc i hi
  have hL := (hc u a).1
  clear hc
  have ha := sepElt_of_ok l.pr u
  have hne : ∀ v : (B.primes X).vT u, conjPrime₂ v.1 ≠ v.1 := fun v => (moveHyp_of_ok l.pr u v).ne
  have hT : ∀ v : (B.primes X).vT u, ((B.T u : ℕ) : 𝓞 B.fields.E) ∈ v.1.asIdeal := fun v => Formalism.L2.Col.T_mem l.pr u v
  have hl := (l.fmL u a).lev i
  let d : (I.stp u a i).Cl → Deco B.fields.E (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs :=
    fun c => ((I.stp u a i).rep c).1.1.deco.1
  have hd : ∀ c, (d c).Ok := fun c => ((I.stp u a i).rep c).1.1.deco.2
  have hs : ∀ x : B.fields.E, (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) x = star x := fun _ => rfl
  have hD0 := fun L => @dualL_one B.fields.E B.fields.fieldE B.fields.nfE B.fields.starE _ _ hs _ hg L
  have hD : ∀ c, LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) = (d c).Lsh := fun c =>
    (hD0 _).trans (congrArg _ (hL c))
  have hPv : ∀ v : (B.primes X).vT u, PvG (D := I.rec7 l Z) (I.resT l u a) v = v.1.asIdeal := fun v =>
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem (I := (v.1.asIdeal : Ideal (𝓞 B.fields.E)))
  have hK : ∀ (v : (B.primes X).vT u) c, LkG (I.rec7 l Z) i hi (PvG (D := I.rec7 l Z) (I.resT l u a) v)
      (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) = (d c).L ⊔ v.1.asIdeal • (d c).Lsh := fun v c =>
    congrArg₂ (· ⊔ ·) (hL c) (congrArg₂ (· • ·) (hPv v) (hD c))
  have h1 := fun v c => localization_Lsh_eq_localization_N (hd c) ha v (hD c)
  have h2 := fun v c => localization_sup_eq_localization_dnN (hd c) ha v (hne v) (hK v c)
  have hf : ∀ v c z, (I.fm l u a).fv i v c (proj (h1 v c) z) = (d c).f v z.1 := fun v c z =>
    dual_redL ((hd c).f_smul v) _ (fv_mk hl v c) (h1 v c ▸ le_locP v.1 _ z.2)
  refine ⟨⟨fun v c => proj (h1 v c), fun v c => proj_surj (h1 v c), fun v c => proj_smul (h1 v c),
    fun v c => proj_ker (h1 v c) (hPv v), fun v c z => ?_, fun v c => proj (h2 v c), fun v c => proj_surj (h2 v c),
    fun v c => proj_smul (h2 v c), fun v c => proj_ker (h2 v c) (hPv v), fun v c z hz h => ?_⟩,
    fun v c z h => proj_mk (h1 v c) z h, fun v c z h => proj_mk (h2 v c) z h⟩
  · have e := f_eq_zero_iff (hd c) ha v (z := z.1) (hD c ▸ z.2)
    rw [← hK v c, ← hf v c z] at e
    exact e
  · obtain ⟨t, ⟨e, he, hfe, ht⟩, hte⟩ := te_mk hl v c
    exact (reductionModPrime_levelPrime_smul_eq (hd c) v (hne v) (hT v) ((hd c).Lsh_le_at ha v (hD c ▸ z.2)) ((hf v c z).symm.trans hz) he hfe t ht).trans hte
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldEquivRealSubfieldQuotientTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ResF

variable {D : D7} {u : D.what₂.Word}

theorem conj_conj_host (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

theorem exists_intF (z : 𝓞 D.host.E) (hz : D.host.conj (z : D.host.E) = z) :
    ∃ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF = z := by
  have hF : (z : D.host.E) ∈ D.host.F := (D.host.conjE_mem_hostF_iff _).2 hz
  refine ⟨⟨⟨z, hF⟩, ?_⟩, ?_⟩
  · exact (isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) Subtype.val_injective).mp
      (RingOfIntegers.isIntegral_coe z)
  · rfl

theorem res_algebraMap_surjective (A : AtTTied u) (v : (D.mem u).A.vT) :
    Function.Surjective ((A.res v).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) := by
  intro r
  obtain ⟨y, rfl⟩ := A.res_surj v r
  let cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
  have hcO : ∀ y : 𝓞 D.host.E, ((cO y : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := fun y => rfl
  obtain ⟨t, ht⟩ := exists_intF (D := D) (A.piU + cO A.piU) (by
    push_cast; simp only [hcO, map_add, conj_conj_host]; ring)
  obtain ⟨z, hz⟩ := exists_intF (D := D) (y * cO A.piU + cO y * A.piU) (by
    push_cast; simp only [hcO, map_add, map_mul, conj_conj_host]; ring)
  have htp : t ∉ (A.eV v).1.asIdeal := by
    rw [A.res_v, ht, map_add, A.res_pi, zero_add]; exact A.res_conj v _ rfl
  obtain ⟨s, i, hi, hsi⟩ := ((A.eV v).1.isMaximal).exists_inv htp
  have hi0 : A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) i) = 0 := (A.res_v v i).1 hi
  have hst : A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s) * A.res v (cO A.piU) = 1 := by
    have := congrArg (fun x => A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x)) hsi
    simp only [map_add, map_mul, map_one, hi0, add_zero, ht, A.res_pi, zero_add] at this
    exact this
  refine ⟨s * z, ?_⟩
  simp only [RingHom.comp_apply, map_mul, hz, map_add, A.res_pi, mul_zero, add_zero]
  rw [mul_comm (A.res v y), ← mul_assoc, hst, one_mul]

theorem exists_fv_equiv (A : AtTTied u) (v : (D.mem u).A.vT) :
    ∃ e : (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (A.eV v).1.asIdeal),
      ∀ a : 𝓞 D.host.F, e (A.res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a := by
  have hker : (A.eV v).1.asIdeal = RingHom.ker ((A.res v).comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) := by
    ext x; rw [RingHom.mem_ker]; exact A.res_v v x
  refine ⟨((Ideal.quotEquivOfEq hker).trans
    (RingHom.quotientKerEquivOfSurjective (res_algebraMap_surjective A v))).symm, fun a => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  rfl

theorem fv_equiv_quot : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ v : ((I.rec7 l Z).mem u).A.vT,
  ∃ e : ((I.rec7 l Z).mem u).A.Fv v ≃+* (𝓞 (I.rec7 l Z).host.F ⧸ (F.atT.eV v).1.asIdeal),
    ∀ a : 𝓞 (I.rec7 l Z).host.F, e (F.atT.res v (algebraMap (𝓞 (I.rec7 l Z).host.F) (𝓞 (I.rec7 l Z).host.E) a)) = Ideal.Quotient.mk _ a :=
  by
  intro B X I _ _ l Z u Ch chOf F _ v
  exact exists_fv_equiv F.atT v

end GlobalTheory.Mem.Col2.ResF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RhoStabChiInLL0
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.RatDatRExp

theorem chi_val_small {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hL : R.toLevCh.Is A.μ0) (hV : GlobalTheory.RealGeo.ValKs R) (i : Fin D.R.m) (PP : Pl D.host.E) (hP : PP ∈ R.Pg)
    (u : (kP PP)ˣ) :
    ∃ y : Ks, ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) = D.what₂.embLL (algebraMap Ks D.what₂.LL y) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP PP)
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h
    have h0 : a = 0 := RingOfIntegers.coe_eq_zero_iff.mp h
    apply u.ne_zero
    rw [← ha, h0, map_zero]
  let k : D.host.Eˣ := Units.mk0 _ ha0
  obtain ⟨ι, hι, hint, happ⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι hι hint happ PP
  have hv : PP.valuation D.host.E (k : D.host.E) ≤ 1 := PP.valuation_le_one a
  have hinf := (GlobalTheory.UnramCharUnique.loc_parts he _ hv).1
  obtain ⟨y, hy⟩ := hV i (Formalism.L2.JoinChr.locU he.1 k) hinf
  have h1 := (hL.mu0 i).2 PP e he k (Formalism.L2.JoinChr.locU he.1 k) rfl
  have h2 := hL.chi i PP hP a k u rfl ha.symm
  refine ⟨y⁻¹, ?_⟩
  rw [MonoidHom.inv_apply] at h2
  have h3 : R.chi ((i : ℕ) + 1) PP u = ((R.C.mu0 i).locK PP k)⁻¹ := by rw [← h2, inv_inv]
  rw [h3, Units.val_inv_eq_inv_val, ← h1, hy, map_inv₀, map_inv₀]

end GlobalTheory.Mem.RatDatRExp

namespace GlobalTheory.Mem.RatDatRExp

theorem rhoStab_chiInLL0 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat3 D A3 C.Q.c.F) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (kKs : C.Q.c.F →+* ↥D.LL0) (hk : ∀ x, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap C.Q.c.F D.what₂.LL x), Pins R F cG → GlobalTheory.RealGeo.InGeo g → ∀ j, 1 ≤ j → j ≤ D.R.m → NX.RhoStab (NX.ratDatR R cG kKs hk) j ∧ NX.ChiInLL0 (NX.ratDatR R cG kKs hk) j := by
  intro D G _ _ Pl0 I0 T A3 C _ R F cG B kKs hk hP _ j _ _
  refine ⟨?_, ?_⟩
  · intro g0 x hx
    change (R.FW (NX.idxOf D j)).ρ g0 x ∈ (R.FW (NX.idxOf D j)).WK
    change x ∈ (R.FW (NX.idxOf D j)).WK at hx
    by_cases hK : Formalism.IndefR.FWT.ActKeeps (κ := B.κ) B.O (NX.idxOf D j)
    · obtain ⟨hf, heq⟩ := (B.rhoGeo (NX.idxOf D j)).1 hK g0 ((B.fw.e (NX.idxOf D j)).symm ⟨x, hx⟩)
      rw [LinearEquiv.apply_symm_apply] at heq
      rw [← heq]
      exact Submodule.coe_mem _
    · rw [(B.rhoGeo (NX.idxOf D j)).2 hK g0]
      exact hx
  · intro g0
    change (((R.FW (NX.idxOf D j)).chi g0 : D.what₂.LLˣ) : D.what₂.LL) ∈ D.LL0
    have hL := hP.char.base.lev
    have hW := hP.char.base.grp.chiW
    have hV := hP.keep.valKs
    have hy : ∀ PP : R.Pg, ∃ y : C.Q.c.F,
        ((R.chi ((NX.idxOf D j : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g0 PP)) : ℂˣ) : ℂ) =
          D.what₂.embLL (algebraMap C.Q.c.F D.what₂.LL y) := fun PP =>
      chi_val_small R.toRealDat hL hV (NX.idxOf D j) PP.1 PP.2 _
    choose y hy using hy
    have h1 := hW (NX.idxOf D j) g0
    rw [Finset.prod_congr rfl (fun PP _ => hy PP), ← map_prod, ← map_prod] at h1
    have h2 := D.what₂.embLL.injective h1
    rw [h2, ← hk]
    exact (kKs _).2

end GlobalTheory.Mem.RatDatRExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RieszVectorsPureTensorsInnerEqProd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem

theorem rieszProd_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (v v' : R.MX.Vec) (a a' : R.cX.W), (∀ w, R.prX w (PiTensorProduct.tprod ℂ v) = ⟪a, w⟫_ℂ) → (∀ w, R.prX w (PiTensorProduct.tprod ℂ v') = ⟪a', w⟫_ℂ) → ⟪a', a⟫_ℂ = ∏ τ, ⟪(v τ : R.MX.H τ), (v' τ : R.MX.H τ)⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB hI v v' a a' ha ha'
  classical
  have hp : GlobalTheory.DefLift.AllPlus R.MX := GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) R.MX
  have hbij := GlobalTheory.DefiniteMult.pair_bijective hB.models.inf hp hB.models.cX hB.models.prX
  have m := GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible D _ _ R.MX hp
  haveI : ∀ τ, FiniteDimensional ℂ (R.MX.sm τ) := fun τ => by haveI := (m τ).1; infer_instance
  let b := fun τ => stdOrthonormalBasis ℂ (R.MX.sm τ)
  let c : R.MX.Vec → (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))) → ℂ := fun u f => ∏ τ, ⟪(b τ (f τ)), u τ⟫_ℂ
  have hexp : ∀ u : R.MX.Vec, PiTensorProduct.tprod ℂ u =
      ∑ f, c u f • PiTensorProduct.tprod ℂ (fun τ => b τ (f τ)) := by
    intro u
    conv_lhs => rw [show u = fun τ => ∑ i, ⟪b τ i, u τ⟫_ℂ • b τ i from funext fun τ => ((b τ).sum_repr' (u τ)).symm]
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    exact MultilinearMap.map_smul_univ _ (fun τ => ⟪b τ (f τ), u τ⟫_ℂ) (fun τ => b τ (f τ))
  let B := Basis.piTensorProduct (fun τ => (b τ).toBasis)
  have hB' : ∀ f, B f = PiTensorProduct.tprod ℂ (fun τ => b τ (f τ)) := fun f => by
    simp [B, Basis.piTensorProduct_apply]

  have hw : ∀ g : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), ∃ w, ∀ f : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), R.prX w (PiTensorProduct.tprod ℂ (fun τ => b τ (f τ))) = if f = g then 1 else 0 := by
    intro g
    obtain ⟨w, hw⟩ := hbij.2 (B.coord g)
    refine ⟨w, fun f => ?_⟩
    rw [hw, ← hB', Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hcoef : ∀ g : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), R.prX a (PiTensorProduct.tprod ℂ (fun τ => b τ (g τ))) = starRingEnd ℂ (c v g) := by
    intro g
    obtain ⟨w, hw⟩ := hw g
    have h1 := hI (fun τ => Fin (Module.finrank ℂ (R.MX.sm τ))) b w a
    rw [Finset.sum_eq_single g (fun f _ hf => by rw [hw f, if_neg hf]; simp) (by simp), hw g, if_pos rfl,
      map_one, one_mul] at h1
    rw [← h1, ← inner_conj_symm, ← ha w, hexp v, map_sum]
    rw [Finset.sum_eq_single g (fun f _ hf => by rw [map_smul, hw f, if_neg hf]; simp) (by simp)]
    rw [map_smul, hw g, if_pos rfl, smul_eq_mul, mul_one]
  have h2 := ha' a
  rw [← h2, hexp v', map_sum]
  have hr : ∀ τ, ⟪((v τ : R.MX.sm τ) : R.MX.H τ), ((v' τ : R.MX.sm τ) : R.MX.H τ)⟫_ℂ =
      ∑ i, ⟪v τ, b τ i⟫_ℂ * ⟪b τ i, v' τ⟫_ℂ := fun τ =>
    (Submodule.coe_inner (R.MX.sm τ) (v τ) (v' τ)).symm.trans ((b τ).sum_inner_mul_inner (v τ) (v' τ)).symm
  have hprod : ∏ τ, ⟪((v τ : R.MX.sm τ) : R.MX.H τ), ((v' τ : R.MX.sm τ) : R.MX.H τ)⟫_ℂ =
      ∑ f : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), ∏ τ, (⟪v τ, b τ (f τ)⟫_ℂ * ⟪b τ (f τ), v' τ⟫_ℂ) := by
    exact (Finset.prod_congr rfl fun τ _ => hr τ).trans
      (Fintype.prod_sum (fun τ (i : Fin (Module.finrank ℂ (R.MX.sm τ))) => ⟪v τ, b τ i⟫_ℂ * ⟪b τ i, v' τ⟫_ℂ))
  refine Eq.trans ?_ hprod.symm
  refine Finset.sum_congr rfl fun f _ => ?_
  have e1 : R.prX a (c v' f • PiTensorProduct.tprod ℂ (fun τ => b τ (f τ))) = c v' f * starRingEnd ℂ (c v f) :=
    ((R.prX a).map_smul _ _).trans ((congrArg (c v' f • ·) (hcoef f)).trans (smul_eq_mul _ _))
  refine e1.trans ?_
  have e2 : starRingEnd ℂ (c v f) = ∏ τ, ⟪v τ, b τ (f τ)⟫_ℂ :=
    (map_prod (starRingEnd ℂ) _ _).trans (Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _)
  refine (congrArg (c v' f * ·) e2).trans ?_
  refine (Finset.prod_mul_distrib).symm.trans ?_
  exact Finset.prod_congr rfl fun τ _ => mul_comm _ _

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurPairingInvariantUnderStandardGroup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.SchurPairingInvariant

theorem left_inv_of_mem_Minf {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {n : ℕ}
    {P : principalLevelFrame.RowPsi V n} {x : MMap M} (hx : x ∈ principalLevelFrame.Minf θ P M) (v : M.Vec) :
    ∀ γ ∈ GQ V, ∀ g, x v (γ * g) = x v g := by
  unfold principalLevelFrame.Minf at hx
  refine Submodule.iSup_induction _ (motive := fun z : MMap M => ∀ γ ∈ GQ V, ∀ g, z v (γ * g) = z v g) hx ?_ ?_ ?_
  · intro N z hz
    exact (PeterssonHilbertSpace.mult_cont_left M θ _ _ hz v).2
  · intro γ _ g
    rfl
  · intro z w hz hw γ hγ g
    simp only [MultilinearMap.add_apply, Pi.add_apply, hz γ hγ g, hw γ hγ g]

theorem ipM_congr_of_iff {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} {T T' U U' : MMap M} (h : ∀ c, IsMultIP M μ 𝓕 T T' c ↔ IsMultIP M μ 𝓕 U U' c) :
    ipM M μ 𝓕 T T' = ipM M μ 𝓕 U U' := by
  have e : IsMultIP M μ 𝓕 T T' = IsMultIP M μ 𝓕 U U' := funext fun c => propext (h c)
  unfold ipM
  rw [e]

theorem ipM_actM : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (n : ℕ) (P : principalLevelFrame.RowPsi V n) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurAll D → V.SigOK → IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (h : Formalism.AUTREP.GAf D.host.E n), ∀ x ∈ principalLevelFrame.Minf θ P M, ∀ y ∈ principalLevelFrame.Minf θ P M, ipM M μ 𝓕 (principalLevelFrame.actM P M h x) (principalLevelFrame.actM P M h y) = ipM M μ 𝓕 x y := by
  intro D V S θ M n P μ 𝓕 _ _ _ hμ h𝓕 h x hx y hy
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  apply ipM_congr_of_iff
  intro c
  have key : ∀ v v' : M.Vec, _ := fun v v' =>
    GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun g => star (x v g) * y v' g) (P.ψ h) h𝓕
      (fun γ hγ g => by simp only [left_inv_of_mem_Minf hx v γ hγ g, left_inv_of_mem_Minf hy v' γ hγ g])
  unfold IsMultIP
  simp only [principalLevelFrame.actM_apply]
  constructor
  · intro H v v'
    obtain ⟨k1, k2⟩ := key v v'
    exact ⟨k1.2 (H v v').1, k2 ▸ (H v v').2⟩
  · intro H v v'
    obtain ⟨k1, k2⟩ := key v v'
    exact ⟨k1.1 (H v v').1, k2.trans (H v v').2⟩

end GlobalTheory.SchurPairingInvariant
end
end

