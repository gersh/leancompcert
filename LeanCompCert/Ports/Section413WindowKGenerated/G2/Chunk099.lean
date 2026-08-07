import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk099

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360773572439630494, 360773572972278653⟩, ⟨(-1918768716412033272), (-1918765141876730310)⟩, true⟩

def state01 : KState := ⟨⟨360797315497474818, 360797316031247162⟩, ⟨(-2154134938826289388), (-2154131353155707536)⟩, true⟩

def words00 : List Nat := [360579807643539475, 360579827322565215, 360579841766671339, 360579856207873993, 360579863837124167, 360579878229836988, 360579902794677124, 360579927354581895, 360579946570663801, 360579968502929565]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 9900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 9900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360698972211177208, 360698972746081534⟩, ⟨(-1179397466578249278), (-1179393869684145946)⟩, true⟩

def words01 : List Nat := [360579986167244042, 360580003828030639, 360580025732661858, 360580037581952513, 360580040970183092, 360580044357739941, 360580053866090403, 360580070248662731, 360580082234900729, 360580094218747178]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 9910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 9900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360874788921196595, 360874789457240993⟩, ⟨(-2925093463337465013), (-2925089855128067631)⟩, true⟩

def words02 : List Nat := [360580100986989285, 360580108964234830, 360580127083360294, 360580145198869205, 360580160502475892, 360580176245327401, 360580186946177976, 360580197644885526, 360580218474715220, 360580248136615873]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 9920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 9900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360638025713954658, 360638026251130806⟩, ⟨(-572323189643001892), (-572319570189578372)⟩, true⟩

def words03 : List Nat := [360580287923765362, 360580327702927058, 360580357430171832, 360580377137864179, 360580394096593152, 360580411051941773, 360580432051004493, 360580443036269410, 360580448829456354, 360580454621497009]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 9930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 9900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360754737542172409, 360754738080481619⟩, ⟨(-1732731426542399520), (-1732727795820655520)⟩, true⟩

def words04 : List Nat := [360580470518919239, 360580491467554610, 360580518352539958, 360580545232142117, 360580562861396178, 360580570492594432, 360580575160295817, 360580579827091906, 360580594583289912, 360580612083514415]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 9940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 9900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360725831587688531, 360725832127142492⟩, ⟨(-1445013306276792661), (-1445009664159179561)⟩, true⟩

def words05 : List Nat := [360580623847508946, 360580635609152580, 360580652439314378, 360580677064131826, 360580695088679635, 360580713109626101, 360580725951505222, 360580736267468486, 360580750835423498, 360580765400492640]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 9950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 9900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360756523950420167, 360756524491008509⟩, ⟨(-1751307086293882433), (-1751303432872115289)⟩, true⟩

def words06 : List Nat := [360580779421072777, 360580790431615369, 360580795220334992, 360580800008105561, 360580802073220081, 360580812104388982, 360580832183629126, 360580852258865802, 360580867175651136, 360580884792595901]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 9960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 9900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360768903429041050, 360768903970765947⟩, ⟨(-1874951552342220647), (-1874947887583344623)⟩, true⟩

def words07 : List Nat := [360580903185246043, 360580921574243257, 360580949998052927, 360580968481798702, 360580978136687724, 360580987789648764, 360580998699495512, 360581014614136726, 360581033440823424, 360581052263764310]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 9970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 9900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360735459195572585, 360735459738447606⟩, ⟨(-1541201144642453780), (-1541197468399639036)⟩, true⟩

def words08 : List Nat := [360581066117029055, 360581084562718869, 360581108894238633, 360581133220920263, 360581154839389238, 360581166538750496, 360581173105437312, 360581179670823273, 360581185717448298, 360581201158886037]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 9980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 9900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360525029259002605, 360525029803013973⟩, ⟨562709426242510145, 562713113843161073⟩, true⟩

def words09 : List Nat := [360581222425642087, 360581243688164697, 360581259831055870, 360581272258009190, 360581282000160154, 360581291740396316, 360581304187975881, 360581306741858045, 360581306741967271, 360581301114398290]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 9990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 9900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 9900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk099
