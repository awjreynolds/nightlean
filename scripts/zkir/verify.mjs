import { readFile, writeFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { Zkir } from '@midnightntwrk/zkir-v3';

const args = process.argv.slice(2);
if (args.length < 1 || args.length > 2) {
  console.error('usage: node verify.mjs INPUT.zkir [OUTPUT.bzkir]');
  process.exitCode = 2;
} else {
  try {
    const source = await readFile(args[0], 'utf8');
    const circuit = Zkir.fromJson(source);
    const k = circuit.getK();
    const serialized = circuit.serialize();
    const roundTrip = Zkir.deserialize(serialized);
    if (roundTrip.getK() !== k) throw new Error('ZKIR serialization changed circuit size');
    if (args[1]) await writeFile(args[1], serialized);
    console.log(JSON.stringify({
      tool: '@midnightntwrk/zkir-v3', version: '3.2.0', input: args[0],
      k, serializedBytes: serialized.length,
      sourceSha256: createHash('sha256').update(source).digest('hex'),
      binarySha256: createHash('sha256').update(serialized).digest('hex'),
      qualification: 'upstream parse, circuit sizing, and binary roundtrip only'
    }));
  } catch (error) {
    console.error(`ZKIR validation failed: ${error.message ?? error}`);
    process.exitCode = 1;
  }
}
