import Foundation
import PDFKit
import AppKit

// Usage: swift INSPECT.swift ABSOLUTE_PDF_PATH EXISTING_OUTPUT_DIRECTORY
let document = PDFDocument(url: URL(fileURLWithPath: CommandLine.arguments[1]))!
let output = URL(fileURLWithPath: CommandLine.arguments[2], isDirectory: true)
let pages = (0..<document.pageCount).map { document.page(at: $0)!.string ?? "" }
let text = pages.enumerated().map { "PAGE \($0.offset + 1)\n\($0.element)\n" }.joined()
try text.write(to: output.appendingPathComponent("pdf-text.txt"),
               atomically: true, encoding: .utf8)
guard let first = pages.firstIndex(where: { $0.contains("What the two self-interpretation") }),
      let last = pages.lastIndex(where: { $0.contains("Formalization status and next obligations") })
else { fatalError("Discussion boundary headings not found in extracted PDF text") }
precondition(first <= last)
print("Pages: \(document.pageCount); discussion inspection: \(first + 1)...\(last + 1)")
for index in first...last {
    let thumbnail = document.page(at: index)!.thumbnail(
        of: NSSize(width: 1050, height: 1485), for: .mediaBox)
    let bitmap = NSBitmapImageRep(data: thumbnail.tiffRepresentation!)!
    try bitmap.representation(using: .png, properties: [:])!.write(
        to: output.appendingPathComponent("page\(index + 1).png"))
    print("Rendered page \(index + 1)")
}
