import createMarmeladeModule from "./marmelade.mjs";

const output = document.querySelector("#output");
const write = line => {
  output.hidden = false;
  output.append(`${line}\n`);
};

const marmelade = await createMarmeladeModule({
  print: write,
  printErr: write,
});

marmelade._marmelade_start();
