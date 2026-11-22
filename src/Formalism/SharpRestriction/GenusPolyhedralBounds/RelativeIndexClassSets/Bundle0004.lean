import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AlgebraMapOlInjective
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LogSupSumLeOfNonvanishingDetLimit
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGap
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0008

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ConclOfHyp
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem thm0Concl : Thm0Concl (D := D) (B := B) (P := P) (j := j) := thm0Concl_of thm0Local

theorem concl_of_hyp (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ)
    (r : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hH : Hyp large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus)
    (hc : 0 ≤ cc D large₂ H.Cc H.Ac H.CRc wL)
    (hr0 : ∀ la, 0 ≤ r la) (hrs : Summable (fun la => r la * X.lN la)) (hrb : (∑' la, r la * X.lN la) ≤ β)
    (hloc : ∀ la (e : ℕ), (T : ℝ) * nus la ≤ (e : ℝ) →
      ∃ L : LocDat X ka la, L.Ok S wL wF T e ∧ L.err T (cc D large₂ H.Cc H.Ac H.CRc wL) ≤ r la) :
    Concl X S ka wL wF T nus β := by
  have hT : 1 ≤ T := by
    obtain ⟨_, hS, _⟩ := hH
    exact (hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 : 0 < T)
  exact thm0Concl large₂ X H S ka wL wF T nus β r hH.2.2.2.1 hT hc
    (theta_le_msup_of_hyp X S hH) hr0 hrs hrb hloc

end Formalism.MainNotions.Gaps.T0
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.GlobalFamilyData
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def etWt (D : D7) (j i : ℕ) : WeightFamilies.Wt D j :=
  wscalar D j (g0 D * i) (by unfold g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩)

def a0 (D : D7) (j T : ℕ) : ℕ := T - WeightFamilies.dimY D j

def ga0 (wL : WeightFamilies.Wt D j) : ℝ :=
  (if h : 0 < (D.R.sigW j).1 then
      (⨅ τ, (wL.aP τ ⟨(D.R.sigW j).1 - 1, by omega⟩ : ℝ)) else 0) +
    (if h : 0 < (D.R.sigW j).2 then
      (⨅ τ, (wL.aM τ ⟨(D.R.sigW j).2 - 1, by omega⟩ : ℝ)) else 0) + wL.n

structure GlobalFamilyData (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) where
  N : ℕ
  w : Fin N → B.Cusp j wL
  del : ℕ
  th' : Fin del → B.Cusp j wF
  rz : ℕ
  alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ
  th0 : Fin rz → B.Cusp j (X.wF0 wL wF)
  zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka
  rq : ℕ
  th : Fin rq → B.Mlat j ka
  iet : ℕ
  et : B.Cusp j (etWt D j iet)

  mx : (B.KO →+* ℂ) → ℝ

namespace GlobalFamilyData

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF)

def Tied (large₂ : SizeData₂ D) (S : Scal B) (CRm : ℝ) (T : ℕ) (c Gc Prw Ch Ah Cf Af : ℝ) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range G.w) = X.WWc S.sW wL ∧ (∀ k, G.w k ∈ B.Mlat j wL) ∧
  Real.log G.N ≤ Prw * (wL.size - 1) ∧
  (∀ σ k, Real.log (B.supN j wL σ (G.w k)) ≤ G.mx σ) ∧
  (∑ σ, G.mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ Gc * wL.size ∧
  (∀ i, G.th' i ∈ X.Thc S.sF wF ∧ WeightFamilies.meanLogSup B (G.th' i) ≤ Gc * wF.size) ∧
  (∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF) ∧ G.th0 k ∈ B.Mlat j (X.wF0 wL wF) ∧
    WeightFamilies.meanLogSup B (G.th0 k) ≤ Gc * (X.wF0 wL wF).size ∧ ∑ i, G.alz k i = a0 D j T) ∧
  (∀ k β, X.inc ka (G.zc k β) = (Formalism.MainNotions.Gaps.SizeBoundsAlt.zPoly X G.w (G.alz k) (G.th0 k)).coeff β) ∧
  (∃ φ : Fin G.rz → B.Cusp j ka →ₗ[B.KO] B.KO, Formalism.MainNotions.Gaps.SizeBoundsAlt.detPoly φ G.zc ≠ 0) ∧
  G.rq = WeightFamilies.rhoP B CRm T c j ka ∧
  (∀ i, ((G.th i : B.Mlat j ka) : B.Cusp j ka) ∈ X.Thc S.sK ka) ∧
  Submodule.span B.KO (Set.range fun i => ((G.th i : B.Mlat j ka) : B.Cusp j ka)) ⊔
    WeightFamilies.MggK B CRm T c j ka = ⊤ ∧
  (∀ i, WeightFamilies.meanLogSup B ((G.th i : B.Mlat j ka) : B.Cusp j ka) ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) ∧
  (j < D.R.m → 0 < G.iet ∧ G.et ≠ 0 ∧ X.NonZeroComp _ G.et ∧
    (∀ la (y : X.Pt la), ((2 * G.iet * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ G.et)) ∧
    ∀ σ, Real.log (B.supN j _ σ G.et) / G.iet ≤ WeightFamilies.PPv D large₂ Cf Af)

end GlobalFamilyData

def DeepIn (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (large₂ : SizeData₂ D) (CG AG Pd : ℝ) : Prop :=
  (∃ (dH : ℕ) (Hm : Formalism.MainNotions.Gaps.SizeBoundsAlt.Herm (fun σ => B.l2NormAlt j ka σ) dH), Hm.Conj) ∧ Formalism.MainNotions.Gaps.SizeBoundsAlt.SubMul X ∧
  Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd ∧ WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) ≤ Pd

def LAMw (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (C A : ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (ka : WeightFamilies.Wt D j) (F : B.Cusp j ka), F ∈ B.Mlat j ka → F ≠ 0 →
    -(WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size) ≤ WeightFamilies.meanLogSup B F

def AdmW (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq : ℝ) : Prop :=
  adm1 B ∧ adm2 large₂ X H.CA H.C1 H.A1 K.CG K.AG ∧ adm3 large₂ X H.CA K.Cf K.Af ∧ ArchimedeanSignatureMatching large₂ X H.CA H.C1 H.A1 K.CW K.AW ∧
    LAMw large₂ B K.CL K.AL ∧ adm6 B K.CRm ∧ adm7 large₂ B K.CRm H.CK Ch Ah Cq Aq

def Shares (D : D7) {j : ℕ} (wL : WeightFamilies.Wt D j) (del rz rq d T : ℕ) (CRm c : ℝ) : Prop :=
  (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * del ≤ d ∧
  (rz : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T ∧
  (rq : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def PolyDom (D : D7) {j : ℕ} (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (C2 A2 CR Ch Ah Cq Aq : ℝ)
    (Gc PH Prw Pet Pd : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  2 ≤ K.CRm ∧ 0 ≤ CR ∧ 0 ≤ Gc ∧ 0 ≤ Prw ∧ 0 ≤ WeightFamilies.PP0v D large₂ K.CL K.AL ∧ WeightFamilies.Obound B large₂ Ch Ah ∧
  WeightFamilies.RRv D H.CRc * WeightFamilies.PPv D large₂ H.Cc H.Ac ≤ WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ∧
  WeightFamilies.RRv D K.CRm * D.host.rdE ^ 2 ≤ WeightFamilies.RRv D CR ^ 2 ∧
  2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 ∧ 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f ∧
  (2 * Gc + 6 * PH + Prw) * 25 ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  Pet ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂) ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  60 * Gc + 180 * PH + 44 * (2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) +
      22 * (2 * WeightFamilies.PPv D large₂ Cq Aq) ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * (WeightFamilies.dimY D j : ℝ) ∧
  1 / 2 ≤ Prw ∧ Prw ≤ PH ∧ 0 ≤ Pet ∧
  Prw ≤ WeightFamilies.PPv D large₂ C2 A2

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ParOfEqBase
section
noncomputable section

namespace Formalism.MainNotions.Gaps.LG

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.MainNotions.Inhab
open scoped TensorProduct

section HostC

variable {R : Ranks} (H : Host R) (T0 : ℕ) [hT0 : Fact T0.Prime] (pz0 : 𝓞 H.E)
  (hpz0 : (pz0 : H.E) * H.conj (pz0 : H.E) = (T0 : H.E))

theorem parOf_eq_base (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E) :
    (letI := H.cmStar; parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz (fun i => H.conj (piG i : H.E))) = hostPar H T pz piG := by
  let _ := H.cmStar
  simp only [parOf, hostPar, Par.mk.injEq, and_true]
  exact ⟨signature_eq_conjugation H T0 pz0 hpz0, gram_matrix_zero_eq_one H T0 pz0 hpz0⟩

def latOfBase (T : ℕ) (pz : 𝓞 H.E) (a : Fin 2 → H.E)
    (S : (letI := H.cmStar; parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz a).Splits)
    [Finite ((letI := H.cmStar; parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz a).Cls S)] (d : ℕ) (hd : 0 < d) :
    letI := H.cmStar
    ∀ i, (clsPkg ((parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz a).Cls S) d hd).cls i →
      Submodule (𝓞 H.E) ((hostSpacesOfNorm H T0 pz0 hpz0).X i).V :=
  letI := H.cmStar
  fun i => match i with
  | 0 => fun c => latBack (hostSpacesOfNorm H T0 pz0 hpz0)
      (CS.globLat ((Quotient.out c : (parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz a).GA) :
        GL (Fin R.k) (H.E ⊗[H.F] FiniteAdeleRing (𝓞 H.F) H.F)) (parOf (hostSpacesOfNorm H T0 pz0 hpz0) H.g T pz a).Lb)
  | _ + 1 => fun c => Empty.elim c

end HostC

set_option maxHeartbeats 800000 in

theorem levGap5_of (h1 : FactSplitG) (h2 : FactLb) (h3 : FactFMCard) (h4 : FactIwLe) (h5 : FactUCompact)
    (h6 : FactUOpen) (h7 : FactClsFinite) (h8 : FactStabTriv) (h9 : FactTNeG) (h10 : FactPlacesT)
    (h11 : FactTau) : Formalism.MainNotions.Inhab.LevelGap := by
  intro R H W _ u0 T hT hlev hpde pz hK hpz hcong hpi
  letI := H.cmStar
  choose piG hpiK hpiN using hpi
  have hd : 0 < minkM (2 * R.f * R.N R.m) := asm_minkM_pos _
  by_cases hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E
  · have hyp : ∀ u, LevHyp H (T u) (pz u) piG := fun u => ⟨(hT u).out, hK u, hpz u, hcong u, hpiK, hpiN, hg⟩
    have ok : ∀ u, (parOf (hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)) H.g (T u) (pz u)
        (fun i => H.conj (piG i : H.E))).AllOK (2 * R.f) := by
      intro u
      rw [parOf_eq_base]
      exact ⟨⟨fun i v h => Classical.choice (h1 H (T u) (pz u) piG (hyp u) i v h)⟩, h2 H (T u) (pz u) piG (hyp u),
        h3 H (T u) (pz u) piG (hyp u), h4 H (T u) (pz u) piG (hyp u), h5 H (T u) (pz u) piG (hyp u),
        h6 H (T u) (pz u) piG (hyp u), h7 H (T u) (pz u) piG (hyp u), h8 H (T u) (pz u) piG (hyp u)⟩
    have hS : ∀ u, Nonempty (parOf (hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)) H.g (T u) (pz u)
        (fun i => H.conj (piG i : H.E))).Splits := fun u => (ok u).splits
    let S := fun u => Classical.choice (hS u)
    haveI : ∀ u, Finite ((parOf (hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)) H.g (T u) (pz u)
        (fun i => H.conj (piG i : H.E))).Cls (S u)) := fun u => (ok u).fin (S u)
    have heT : ∀ u, Nonempty (Fin R.f ≃ PlT H (T u)) := fun u => h10 H (T u) (pz u) piG (hyp u)
    let eT := fun u => Classical.choice (heT u)
    have hTg : ∀ u i, Nat.Coprime (T u) (H.g i) := fun u i =>
      (Nat.coprime_primes (hT u).out (H.g_prime i)).2 (h9 H (T u) (pz u) piG (hyp u) i)
    have htau0 : ∀ u (w : HeightOneSpectrum (𝓞 H.E)), ∃ e : Fin R.f ≃ ↥(R.Psi), PlacesToy.resCharW w = T u →
        ∀ (v : Fin R.f) (x : 𝓞 H.F), x ∈ (eT u v).1.asIdeal ↔
          (0 : WithTop ℤ) < PlacesToy.valW w (H.sigmaOf (e v : R.GG) (algebraMap H.F H.E (x : H.F))) := by
      intro u w
      by_cases h : PlacesToy.resCharW w = T u
      · obtain ⟨e, he⟩ := h11 H (T u) (pz u) piG (hyp u) w (h ▸ PlacesToy.resCharW_mem w)
        exact ⟨(eT u).trans e, fun _ v x => (he (eT u v) x).trans (valW_pos_iff _ _).symm⟩
      · exact ⟨Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_realPlaces_eq_degree]), fun hh => absurd hh h⟩
    choose tauF htau using htau0
    refine ⟨fun u => clsPkg ((parOf (hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)) H.g (T u) (pz u)
        (fun i => H.conj (piG i : H.E))).Cls (S u)) (minkM (2 * R.f * R.N R.m)) hd,
      fun _ _ => ⟨fun c => Empty.elim c⟩, fun _ => rfl,
      fun u => latOfBase H (T u0) (pz u0) (hpz u0) (T u) (pz u) _ (S u) (minkM (2 * R.f * R.N R.m)) hd, ?_, ?_⟩
    · intro u i c
      match i, c with
      | 0, c =>
        exact latBack_isLattice _ _
          (Formalism.UG.P.global_lattice_isLattice_holds H.F H.E (Fin R.k) _ (ok u).lb.fin (ok u).lb.span _)
      | _ + 1, c => exact Empty.elim c
    · intro hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol Dst hD du hdu Gam hG hwin
        hg' ht G kb ks tw htw
      refine levGapD_gen _ pz piG ?_ ?_ ?_ ?_ ?_ ?_ S (fun _ => Equiv.refl _) ?_ ?_ ?_
        eT tauF ?_
      · exact hK
      · exact hpz
      · exact hcong
      · exact hpiK
      · exact hpiN
      · exact ok
      · exact fun _ _ => inferInstanceAs (Subsingleton Unit)
      · exact fun _ c => crdLat0_latBack _ _
      · exact hTg
      · exact fun u w hw v x => htau u w hw v x
  · refine ⟨fun _ => clsPkg Empty (minkM (2 * R.f * R.N R.m)) hd, fun _ _ => ⟨fun c => Empty.elim c⟩, fun _ => rfl,
      fun _ i => match i with
        | 0 => fun c => Empty.elim c
        | _ + 1 => fun c => Empty.elim c, ?_, ?_⟩
    · intro _ i c
      match i, c with
      | 0, c => exact Empty.elim c
      | _ + 1, c => exact Empty.elim c
    · intro hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol Dst hD du hdu Gam hG hwin
        hg' ht G kb ks tw htw
      exact absurd hg' hg

theorem levGap5 : Formalism.MainNotions.Inhab.LevelGap :=
  levGap5_of factSplitG Formalism.MainNotions.Gaps.LevGap.factLb factFMCard factIwLe Formalism.MainNotions.Gaps.LevGap.factUCompact
    Formalism.MainNotions.Gaps.LevGap.factUOpen factClsFinite factStabTriv Formalism.MainNotions.Gaps.LevGap.factTNeG
    Formalism.MainNotions.Gaps.LevGap.factPlacesT Formalism.MainNotions.Gaps.LevGap.factTau

end Formalism.MainNotions.Gaps.LG

end
end

