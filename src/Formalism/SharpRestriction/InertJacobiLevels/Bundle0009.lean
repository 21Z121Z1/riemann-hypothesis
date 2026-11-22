import Formalism.SharpRestriction.InertJacobiLevels.Bundle0008
import Formalism.LocalRingCardinality.DataParams

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExistsLarge
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

theorem FC.Large.mono {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large K' CH) (hK : K.le K') : C.Large K CH :=
  ⟨fun c hc => hK.1.trans (h.1 c hc), trivial, fun c hc => (hK.2.2.1 _).trans (h.2.2.1 c hc),
    fun c hc => (hK.2.2.2 _).trans (h.2.2.2 c hc)⟩

def fcOf (p t : ℝ) (o : Out) (M N : ℝ) : FC where
  Ct := t
  Cc := o.Cc
  CT2 := o.CT2
  CGam := M
  Csz := M
  Cr := 1
  CTu := o.CTu
  Cdg := o.Cdg
  C5 := o.C5
  full := o.full
  GK := ⟨M, N, N, N, N, N, N, N, N, N, N, 5, 4, 1, N⟩
  cX := ⟨1, ⟨12, 3, M⟩⟩
  P := ⟨N, N, N, N⁻¹, 10, N, N, o.CLw, o.Cj0, N, o.cw, N, N, N, N, N, N, o.CetaF, N, o.CYL, o.Cpde, o.CccK, M⟩
  T := ⟨p, o.eP, o.Cp, N, o.cTO, N, N⟩

theorem exists_large (K : TransportedAlt) (out : ℝ → ℝ → Out) :
    ∃ (C : FC) (CH : ℝ), 0 ≤ CH ∧ C.out = out C.T.CP C.Ct ∧ C.GK.Nonneg ∧ 1 ≤ C.Cr ∧ C.Large K CH ∧ C.P.CF = CH ∧
      C.GK.Pr1 = 1 ∧ C.GK.dl1 = 5 ∧ C.GK.dl2 = 4 ∧ C.cX.Ce = 1 ∧ C.cX.err.c6 = 12 ∧ C.cX.err.dig = 3 ∧ C.Cr = 1 ∧
      C.P.CnW = 10 ∧ C.Ct = 401 := by
  set p := K.pre with hp
  set t : ℝ := 401 with ht
  set o := out p t with ho
  set M := max (K.mid (fcOf p t o 0 0).cOut) 1 with hM
  set N := max (K.last ((fcOf p t o 0 0).cOut ++ (fcOf p t o M 0).cMid M)) 1 with hN
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  have hN0 : 0 ≤ N := le_trans zero_le_one (le_max_right _ _)
  refine ⟨fcOf p t o M N, M, hM0, rfl, ⟨hM0, hN0, hN0, hN0, hN0, hN0, hN0, hN0, hN0, hN0, hN0, by show (0 : ℝ) ≤ 5; norm_num, by show (0 : ℝ) ≤ 4; norm_num,
      by show (0 : ℝ) ≤ 1; norm_num, hN0⟩,
    le_refl _, ⟨?_, trivial, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro c hc
    have hc' : c = p := by
      simp only [FC.cPre, fcOf, List.mem_cons, List.not_mem_nil, or_false] at hc
      exact hc
    rw [hc']
  · intro c hc
    have hc' : c = M := by
      simp only [FC.cMid, fcOf, List.mem_cons, List.not_mem_nil, or_false, or_self] at hc
      exact hc
    rw [hc']
    exact le_max_left _ _
  · intro c hc
    have hc' : c = N := by
      simp only [FC.cLast, fcOf, List.mem_cons, List.not_mem_nil, or_false, or_self, inv_inv] at hc
      exact hc
    rw [hc']
    exact le_max_left _ _

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExtraF
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions Formalism.FrobeniusOrbits NumberField IsDedekindDomain

section

variable {R : Ranks} (H : Host R) (hc : Tau2 R → HCParam R) (etaF : ℝ) (Dn : ℕ) (hDel : (0 : ℚ) < (Dn : ℚ))
  (hgap : ∀ (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hc τ).v ⟨l, by omega⟩ - (hc τ).v ⟨l + 1, h⟩ = 4 * (Dn : ℚ))
  (hlet : ∀ (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hc τ).u ⟨l + 1, by omega⟩ = (hc τ).v ⟨l, by omega⟩ - 1 / 2)
  (hu : ∀ τ, FdegUniq R (hc τ))
  (hv : ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ W, 0 < vol W) (K : ClsPkg)
  (T : ℕ) [hT : Fact T.Prime] (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)
  (hwin : (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar ≤ (T : ℝ) ∧
    (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (mem3 hc K T Dst hD du hdu Gam hG).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ i, K.cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H T pz hpz).X i).V)
  (hlat : letI := H.cmStar; ∀ i c, Submodule.IsLattice H.E (lat i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

def d7F : D7 := twistRecord H hc (Dn : ℚ) hDel hgap hlet (CD.cdScaleOf CD.cdHaar) (CD.cdScaleOf_pos _) (fun τ => (hu τ).choose) (fun τ => (hu τ).choose_spec.1) etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw

theorem trivialFamily_shape_zero (hE : ∀ i, IsEmpty (K.cls (i + 1))) (hDG : K.DGam = minkM (2 * R.f * R.N R.m)) : Shape0 (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) := shape_zero_trivialDatum H hc (Dn : ℚ) hDel hgap hlet (CD.cdScaleOf CD.cdHaar) (CD.cdScaleOf_pos _) (fun τ => (hu τ).choose) (fun τ => (hu τ).choose_spec.1) etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw hE hDG

theorem trivialFamily_rank_zero (u) : Module.finrank ℂ ((d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).mem u).A.Mu0 = 0 := trivialDatum_finrank_zero H hc (Dn : ℚ) hDel hgap hlet (CD.cdScaleOf CD.cdHaar) (CD.cdScaleOf_pos _) (fun τ => (hu τ).choose) (fun τ => (hu τ).choose_spec.1) etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw u

theorem trivialFamily_embedding_bijective : Function.Bijective (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).embE := Function.bijective_id

theorem trivialFamily_compatibilities (W : TwGap (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw)) : Ties (withTw (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) W) :=
  ties_withTw _ W rfl (fun τ V _ _ σ d h1 h2 => (hu τ).choose_spec.2 V σ d h1 h2)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) ⟨fun x => Empty.elim x⟩

theorem trivialFamily_dualStar_eq (h : (du : ℝ) = duStarH H hc) (u) :
    (((d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).mem u).A.duStar : ℝ) = StandardLattice.duStarU (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) u := h

theorem trivialFamily_discriminantStar_eq (hvl : vol = fun _ => volFor R H.g (fun τ => (hu τ).choose) Dst) :
    (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).what₂.Dstar = StandardLattice.DstarD (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) := by
  subst hvl
  exact dstar_def_of_vol _ rfl

theorem trivialFamily_kappaDef_congr (hv' : ℝ) (h : DV.KapDef (d7F H hc etaF Dn hDel hgap hlet hu hv' vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw)) :
    DV.KapDef (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) := h

theorem trivialFamily_exists_kappa : ∃ kb ks, DV.KapDef (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) :=
  twistRecord_weights_defined H hc (Dn : ℚ) hDel hgap hlet (CD.cdScaleOf CD.cdHaar) (CD.cdScaleOf_pos _) (fun τ => (hu τ).choose) (fun τ => (hu τ).choose_spec.1) etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G tw htw

set_option maxHeartbeats 2000000 in
theorem trivialFamily_heightValue_eq (hv' : ℝ) (sc : Scale) (aT : H.TT → ℤ) (η Sc dl C : ℝ) (u) :
    hVal (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) sc aT η Sc dl C u = hVal (d7F H hc etaF Dn hDel hgap hlet hu hv' vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) sc aT η Sc dl C u := rfl

theorem trivialFamily_logDerivative_eq (hv' : ℝ) (s : ℂ) :
    dlogL (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) s = dlogL (d7F H hc etaF Dn hDel hgap hlet hu hv' vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw) s := rfl

theorem trivialFamily_divisor_rank_zero : (d7F H hc etaF Dn hDel hgap hlet hu hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw).div.R = 0 := by
  show ∑ u : Unit, (zeroHLat H.E).rank = 0
  simp [zeroHLat_rank]

end

end Formalism.MainNotions.Inhab

end
end

