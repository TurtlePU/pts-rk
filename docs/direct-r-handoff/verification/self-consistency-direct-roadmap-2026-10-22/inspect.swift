import Foundation
import AppKit
import PDFKit

let input = CommandLine.arguments[1]
let output = CommandLine.arguments[2]
guard let document = PDFDocument(url: URL(fileURLWithPath: input)) else {
    fatalError("Unreadable PDF")
}
let pages = (0..<document.pageCount).map { document.page(at: $0)! }
for (index, page) in pages.enumerated() {
    guard let content = page.string,
          !content.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty else {
        fatalError("Empty text on page \(index + 1)")
    }
}
let text = pages.map { $0.string! }.joined(separator: "\n")
let flat = text.replacingOccurrences(of: "-\n", with: "")
    .replacingOccurrences(of: "\n", with: " ")
for needle in ["Adm", "Res", "Acc", "Cons", "Pakhomov", "Elementary",
               "rank", "compression", "resource", "independent",
               "GenericFold", "NativeCanonicity", "not a claim"] {
    guard flat.contains(needle) else { fatalError("Missing text: \(needle)") }
}
guard flat.contains("Raw intermediate terms") else {
    fatalError("Missing raw conversion-intermediate caveat")
}
for artifact in ["\\mathsf", "\\Pi", "\\tag", "$$"] {
    guard !text.contains(artifact) else { fatalError("Unrendered mathematics: \(artifact)") }
}
let links = pages.flatMap { $0.annotations.compactMap { $0.url?.absoluteString } }
guard links.contains("https://arxiv.org/pdf/1907.00877v2") else {
    fatalError("Missing primary-source citation")
}
try text.write(toFile: output + "/text.txt", atomically: true, encoding: .utf8)
for (index, page) in pages.enumerated() {
    let bounds = page.bounds(for: .mediaBox)
    let img = page.thumbnail(of: NSSize(width: bounds.width * 1.4,
                                      height: bounds.height * 1.4), for: .mediaBox)
    guard let data = img.tiffRepresentation,
          let bitmap = NSBitmapImageRep(data: data),
          let png = bitmap.representation(using: .png, properties: [:]) else {
        fatalError("Cannot render page \(index + 1)")
    }
    try png.write(to: URL(fileURLWithPath: output + "/page-\(index + 1).png"))
}
print("PASS: \(document.pageCount) nonempty pages, \(links.count) links; required text, mathematics, all-page rendering")
