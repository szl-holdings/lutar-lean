/-
  Formula ID : A8-05  MAYA-THREE-CLOCK-LCM
  Source     : Maya Long Count calendar system (Classic period,
               ~250–900 CE).  R4 encoded the two-clock Tzolk'in/Haab'
               Calendar Round (lcm 260 365 = 18980).  This stub
               EXTENDS to a three-clock system adding the 360-day Tun
               administrative year: lcm(260, 365, 360) = 341640.
               Ref: Aveni, "Skywatchers of Ancient Mexico" (1980) ch. 7;
               Houston & Stuart, "The Way Glyph" (1989).
  Insight    : Multi-clock LCM governs epoch synchronisation in rosie's
               distributed timer array.  Adding a third clock period
               shows how LCM grows and bounds worst-case re-sync latency.
  Lean target: rosie
  Sorry-free : Yes  (native_decide closes the numeric computation)
  Round      : 8  (R4 had two-clock lcm 18980; this is the three-clock
               extension — distinct formula)
  Namespace  : Lutar.Innovations.Round8.MayaThreeClockLCM
               (OUTSIDE locked kernel c7c0ba17 / 749-14-163)
  SLSA       : L1 honest
  Section 889: not applicable
  Signed-off-by: Yachay <yachay@szlholdings.ai>
  Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/

namespace Lutar.Innovations.Round8.MayaThreeClockLCM

open Nat

/-!
## Maya three-clock LCM — multi-epoch synchronisation

Three Maya cycle lengths:
- 260 : Tzolk'in (sacred calendar)
- 365 : Haab'   (solar calendar)
- 360 : Tun     (administrative year, 18 × 20 days)
-/

/-- Tzolk'in period (days). -/
abbrev tzolkin : ℕ := 260

/-- Haab' period (days). -/
abbrev haab : ℕ := 365

/-- Tun administrative period (days). -/
abbrev tun : ℕ := 360

/-- Three-clock LCM: the first day all three cycles realign. -/
def threeClockEpoch : ℕ := Nat.lcm (Nat.lcm tzolkin haab) tun

/-- The three-clock epoch equals 341640 days. -/
theorem threeClockEpoch_eq : threeClockEpoch = 341640 := by
  native_decide

/-- All three clocks divide the epoch. -/
theorem tzolkin_dvd : tzolkin ∣ threeClockEpoch := by native_decide
theorem haab_dvd    : haab    ∣ threeClockEpoch := by native_decide
theorem tun_dvd     : tun     ∣ threeClockEpoch := by native_decide

/-- Extension fact: the three-clock epoch is larger than the two-clock
    Calendar Round (18980 days), illustrating LCM growth. -/
theorem threeClockExceedsTwoClock :
    threeClockEpoch > Nat.lcm tzolkin haab := by
  native_decide

end Lutar.Innovations.Round8.MayaThreeClockLCM
