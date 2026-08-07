import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk001

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨344405256661344050, 344405256661370381⟩, ⟨1515092119513520055, 1515092119515357135⟩, true⟩

def state01 : KState := ⟨⟨372578107420798219, 372578107420831023⟩, ⟨(-1445303000282797928), (-1445303000280279506)⟩, true⟩

def words00 : List Nat := [359406168735780382, 359335588792657047, 359404423006287860, 359475182540739964, 359475182540740596, 359459627751498293, 359381188793637934, 359376602905183935, 359438989236464093, 359557359670558235]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360510393116884625, 360510393116924948⟩, ⟨(-17696282491279563), (-17696282487894667)⟩, true⟩

def words01 : List Nat := [359622344496466491, 359686179148464973, 359815647171584683, 359988824111894919, 360120400303105588, 360249727328654670, 360331335497165503, 360361684860722543, 360362924096191571, 360364142848429951]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361117112456591960, 361117112456640397⟩, ⟨(-138235074585673894), (-138235074581272688)⟩, true⟩

def words02 : List Nat := [360376161443791032, 360376161443791863, 360339127586401761, 360262209273725977, 360186521654052891, 360096162409295479, 360066549390471622, 360077656845727399, 360077656845728192, 360061882879684117]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨370252272550762473, 370252272550819650⟩, ⟨(-1406824155542368092), (-1406824155536785530)⟩, true⟩

def words03 : List Nat := [360118570357288971, 360174405391621821, 360211629994441888, 360211629994442806, 360207336462137817, 360156825983905345, 360107052884916997, 360131235460625188, 360203528582698771, 360274796270416916]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨356616908858944725, 356616908859011475⟩, ⟨499163771438703415, 499163771445676209⟩, true⟩

def words04 : List Nat := [360316812321722224, 360321338762645610, 360321338762646428, 360311314774934664, 360301429049122150, 360271039415033110, 360204876568800513, 360104272735106746, 360005019288442261, 359944667335315984]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨355446804066379533, 355446804066456384⟩, ⟨715401557446066129, 715401557454606667⟩, true⟩

def words05 : List Nat := [359938050015125553, 359953269251253521, 359953269251254467, 359945928537408227, 359945928537409125, 359936460082194391, 359952382018298761, 359952382018299849, 359946184930949627, 359918063800547676]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361418846558191807, 361418846558279775⟩, ⟨(-287589173291598407), (-287589173281222263)⟩, true⟩

def words06 : List Nat := [359890292000957987, 359851205172078486, 359843852272515794, 359856022194140203, 359856022194141291, 359832111179379576, 359779372587969139, 359758192272550909, 359737262611752712, 359737038527395435]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨359682263267611514, 359682263267711305⟩, ⟨16318719461090463, 16318719473537587⟩, true⟩

def words07 : List Nat := [359737038527396538, 359726330196092323, 359734503214997107, 359773076229987468, 359789091469314192, 359804925745484873, 359804925745485992, 359801645738676030, 359773429298288295, 359772922820342070]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360963037762939137, 360963037763051475⟩, ⟨(-196347594010515185), (-196347593995745037)⟩, true⟩

def words08 : List Nat := [359799057772891294, 359837357752518860, 359857987698409864, 359878394617858961, 359885460501141494, 359908314213706175, 359922706661750467, 359936946808757504, 359936946808758745, 359935039888728203]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨374836077610435986, 374836077610561726⟩, ⟨(-2916971798814639084), (-2916971798797252816)⟩, true⟩

def words09 : List Nat := [359964355043981748, 359993366415243408, 360045823537674567, 360077444903426072, 360086359489856758, 360095183572872072, 360127125777009678, 360177927867859265, 360251218616573962, 360323780104107732]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk001
