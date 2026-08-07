import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk126

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360549988807294046, 360549989690423904⟩, ⟨395915831376096825, 395923369297201927⟩, true⟩

def state01 : KState := ⟨⟨360560761346477595, 360560762231067824⟩, ⟨259972495059689061, 259980051388992371⟩, true⟩

def words00 : List Nat := [360581413460639784, 360581413460794912, 360581410986673422, 360581405360310336, 360581399734814642, 360581392471533969, 360581390070942270, 360581387478377410, 360581384886208292, 360581379205801289]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 12600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 12600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360784641739136368, 360784642625191666⟩, ⟨(-2564149071710334497), (-2564141496899174321)⟩, true⟩

def words01 : List Nat := [360581382192485085, 360581386813321717, 360581397688373577, 360581411863097994, 360581420547709559, 360581429230956877, 360581435887491586, 360581445739502308, 360581461840807628, 360581477939596296]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 12610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 12600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360659034442667883, 360659035330204402⟩, ⟨(-979197062002260279), (-979189468490843001)⟩, true⟩

def words02 : List Nat := [360581489091424518, 360581494007016782, 360581500642540512, 360581507277057610, 360581511622937410, 360581512522485083, 360581512522625050, 360581509118272768, 360581506472664860, 360581512610824239]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 12620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 12600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360479225352945944, 360479226241946502⟩, ⟨1292851884675581919, 1292859496685154991⟩, true⟩

def words03 : List Nat := [360581520732133649, 360581528852186597, 360581533836236803, 360581533836392315, 360581532595712926, 360581526582360556, 360581520789469344, 360581520789624906, 360581517522479085, 360581509429975391]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 12630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 12600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360634726127080067, 360634727017551937⟩, ⟨(-673109842339195392), (-673102211725234204)⟩, true⟩

def words04 : List Nat := [360581501338717164, 360581502760658023, 360581509861187678, 360581516960623983, 360581518844455391, 360581518844611008, 360581516410864218, 360581518305653129, 360581518305781895, 360581521562510816]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 12640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 12600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360670927513985368, 360670928405937836⟩, ⟨(-1131182273690110098), (-1131174624339023440)⟩, true⟩

def words05 : List Nat := [360581522642162266, 360581523721660008, 360581531019122987, 360581542818533390, 360581552992039762, 360581563163966489, 360581570214276194, 360581571061109695, 360581578119477926, 360581585176782239]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 12650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 12600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360633775029617081, 360633775923038896⟩, ⟨(-661000963859209149), (-660993295898757549)⟩, true⟩

def words06 : List Nat := [360581593092139338, 360581599347806580, 360581600305628780, 360581601263312926, 360581601263443792, 360581598293005595, 360581602232146194, 360581606170694547, 360581606170833563, 360581610087990459]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 12660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 12600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360627594273899005, 360627595168792734⟩, ⟨(-582756638778972474), (-582748952161880260)⟩, true⟩

def words07 : List Nat := [360581620405280925, 360581630720991078, 360581639419652593, 360581641930145102, 360581641930289677, 360581639115622146, 360581636301371186, 360581633424506001, 360581637049375694, 360581640673708602]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 12670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 12600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360560683953359458, 360560684849740706⟩, ⟨265293269025901277, 265300974511960555⟩, true⟩

def words08 : List Nat := [360581641064265995, 360581641064422447, 360581639672398505, 360581639147143662, 360581638621927900, 360581634692149532, 360581624589201256, 360581611380639252, 360581598174128762, 360581591151908710]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 12680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 12600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360498695623336251, 360498696521190028⟩, ⟨1052116584024402531, 1052124308204280333⟩, true⟩

def words09 : List Nat := [360581589504704499, 360581586246038854, 360581582987869399, 360581576628143354, 360581569560543375, 360581560877785860, 360581552196350512, 360581549690114094, 360581547478442580, 360581540954906901]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 12690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 12600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 12600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk126
