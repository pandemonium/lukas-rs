// Stdlib.Browser -- the browser side of the DOM builder, events, subscriptions,
// local storage, fetch and web sockets.
//
// An Emscripten JS library: compile-lady.sh passes it with --js-library whenever
// Browser.c is linked into a Wasm build, and Browser.c declares each function
// below extern. State that must outlive a call lives on `Module`.

addToLibrary({
    browser_dom_begin__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_dom_begin: function(root, root_len) {
    const id = UTF8ToString(root, root_len);
    let mount = document.getElementById(id);
    if (!mount) {
        mount = document.createElement("div");
        mount.id = id;
        document.body.appendChild(mount);
    }
    const tree = { kind: "fragment", keyed: false, children: [], keys: [] };
    // Lazy subtrees outlive a render: `lazy` maps an id to the virtual node it was
    // filed under, and `touched` collects the ids this render used or kept, so
    // finish can drop the rest.
    if (!Module.marmeladeLazy) Module.marmeladeLazy = new Map();
    if (!Module.marmeladePush) {
        // Appends a child to the open element, filing it under the pending key
        // when that element is keyed.
        Module.marmeladePush = (dom, node) => {
            const parent = dom.stack[dom.stack.length - 1];
            parent.children.push(node);
            if (parent.keyed) parent.keys.push(dom.pendingKey);
            dom.pendingKey = "";
        };
    }
    Module.marmeladeDom = { mount, tree, stack: [tree], pendingKey: "", touched: new Set() };
},

    browser_dom_open__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_dom_open: function(space, keyed, name, name_len) {
    const dom = Module.marmeladeDom;
    const element = {
        kind: "element",
        space,
        keyed: keyed !== 0,
        name: UTF8ToString(name, name_len),
        attributes: new Map(),
        children: [],
        keys: [],
    };
    Module.marmeladePush(dom, element);
    dom.stack.push(element);
},

    browser_dom_close__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_dom_close: function() {
    const dom = Module.marmeladeDom;
    if (dom.stack.length > 1) dom.stack.pop();
},

    browser_dom_text__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_dom_text: function(body, body_len) {
    Module.marmeladePush(Module.marmeladeDom, {
        kind: "text",
        body: UTF8ToString(body, body_len),
    });
},

    browser_dom_key__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_dom_key: function(key, key_len) {
    Module.marmeladeDom.pendingKey = UTF8ToString(key, key_len);
},

    browser_dom_attribute__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_dom_attribute: function(name, name_len, value, value_len) {
    const dom = Module.marmeladeDom;
    dom.stack[dom.stack.length - 1].attributes.set(
        UTF8ToString(name, name_len), UTF8ToString(value, value_len));
},

    browser_dom_event__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_dom_event: function(name, name_len, index) {
    const dom = Module.marmeladeDom;
    dom.stack[dom.stack.length - 1].attributes.set(
        "data-marmelade-" + UTF8ToString(name, name_len), String(index));
},

    browser_dom_lazy_store__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_dom_lazy_store: function(id) {
    const dom = Module.marmeladeDom;
    const parent = dom.stack[dom.stack.length - 1];
    Module.marmeladeLazy.set(id, parent.children[parent.children.length - 1]);
    dom.touched.add(id);
},

    browser_dom_lazy_reuse__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_dom_lazy_reuse: function(id) {
    const dom = Module.marmeladeDom;
    const virtual = Module.marmeladeLazy.get(id) || { kind: "text", body: "" };
    Module.marmeladePush(dom, virtual);
    dom.touched.add(id);
},

    browser_dom_lazy_keep__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_dom_lazy_keep: function(id) {
    Module.marmeladeDom.touched.add(id);
},

    browser_dom_finish__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_dom_finish: function() {
    const dom = Module.marmeladeDom;
    const SVG = "http://www.w3.org/2000/svg";
    const HTML = "http://www.w3.org/1999/xhtml";

    const updateAttributes = (element, wanted) => {
        for (const name of element.getAttributeNames()) {
            if (!wanted.has(name)) element.removeAttribute(name);
        }
        for (const [name, value] of wanted) {
            if (element.getAttribute(name) !== value) {
                element.setAttribute(name, value);
            }
        }

        // `value` is a live property.  The browser has normally applied an input
        // event's value already, so avoid assigning it when it agrees with the
        // model; assigning even the same value can disturb the caret.
        if (element.localName === "input" && wanted.has("value")) {
            const value = wanted.get("value");
            if (element.value !== value) element.value = value;
        }
    };

    // SVG names are case-sensitive ("linearGradient"); HTML's localName is lower case.
    const sameKind = (node, virtual) => {
        if (virtual.kind === "text") return node.nodeType === 3;
        if (node.nodeType !== 1) return false;
        if (virtual.space === 1) {
            return node.namespaceURI === SVG && node.localName === virtual.name;
        }
        return node.namespaceURI === HTML &&
               node.localName === virtual.name.toLowerCase();
    };

    // Every DOM node remembers the virtual node it was last made to match. A lazy
    // subtree reused from an earlier render is that same object, so it is skipped
    // without being walked.
    const createNode = virtual => {
        let node;
        if (virtual.kind === "text") {
            node = document.createTextNode(virtual.body);
        } else {
            node = virtual.space === 1
                ? document.createElementNS(SVG, virtual.name)
                : document.createElement(virtual.name);
            updateAttributes(node, virtual.attributes);
            virtual.children.forEach((child, index) => {
                const made = createNode(child);
                if (virtual.keyed) made.marmeladeKey = virtual.keys[index];
                node.appendChild(made);
            });
        }
        node.marmeladeVirtual = virtual;
        return node;
    };

    const patch = (node, virtual) => {
        if (node.marmeladeVirtual === virtual) return;
        if (virtual.kind === "text") {
            if (node.nodeValue !== virtual.body) node.nodeValue = virtual.body;
        } else {
            updateAttributes(node, virtual.attributes);
            if (virtual.keyed) reconcileKeyed(node, virtual);
            else reconcileChildren(node, virtual.children);
        }
        node.marmeladeVirtual = virtual;
    };

    const reconcileChildren = (parent, wanted) => {
        for (let index = 0; index < wanted.length; index++) {
            const virtual = wanted[index];
            const current = parent.childNodes[index];
            if (!current) {
                parent.appendChild(createNode(virtual));
            } else if (!sameKind(current, virtual)) {
                parent.replaceChild(createNode(virtual), current);
            } else {
                patch(current, virtual);
            }
        }

        while (parent.childNodes.length > wanted.length) {
            parent.removeChild(parent.lastChild);
        }
    };

    // Match children by key, then put the DOM in the wanted order. Each wanted
    // child is moved to its index, so whatever is left after the last one was not
    // wanted and is removed.
    const reconcileKeyed = (parent, virtual) => {
        const byKey = new Map();
        for (const node of parent.childNodes) {
            if (node.marmeladeKey !== undefined && !byKey.has(node.marmeladeKey)) {
                byKey.set(node.marmeladeKey, node);
            }
        }
        const wanted = virtual.children;
        for (let index = 0; index < wanted.length; index++) {
            const child = wanted[index];
            const key = virtual.keys[index];
            let node = byKey.get(key);
            if (node && sameKind(node, child)) {
                byKey.delete(key);
                patch(node, child);
            } else {
                node = createNode(child);
            }
            node.marmeladeKey = key;
            const current = parent.childNodes[index];
            if (current !== node) parent.insertBefore(node, current || null);
        }
        while (parent.childNodes.length > wanted.length) {
            parent.removeChild(parent.lastChild);
        }
    };

    reconcileChildren(dom.mount, dom.tree.children);

    for (const id of Module.marmeladeLazy.keys()) {
        if (!dom.touched.has(id)) Module.marmeladeLazy.delete(id);
    }

    if (!dom.mount.marmeladeListeners) {
        const mount = dom.mount;
        const ownerFrom = (kind, start) => {
            if (!(start instanceof Element)) return null;
            const owner = start.closest(`[data-marmelade-${kind}]`);
            return owner && mount.contains(owner) ? owner : null;
        };
        const indexOf = (owner, kind) =>
            Number(owner.getAttribute(`data-marmelade-${kind}`));

        const sendText = (index, payload) => {
            const bytes = lengthBytesUTF8(payload) + 1;
            const pointer = _malloc(bytes);
            stringToUTF8(payload, pointer, bytes);
            Module._marmelade_browser_dispatch(index, pointer);
            _free(pointer);
        };

        // Relative to the owner: its user units when it is SVG (so a scaled board
        // answers in board coordinates), otherwise CSS pixels from its corner.
        const pointerFields = (owner, event) => {
            let x, y;
            const matrix = owner instanceof SVGGraphicsElement ? owner.getScreenCTM() : null;
            if (matrix) {
                const point = new DOMPoint(event.clientX, event.clientY)
                    .matrixTransform(matrix.inverse());
                x = point.x;
                y = point.y;
            } else {
                const box = owner.getBoundingClientRect();
                x = event.clientX - box.left;
                y = event.clientY - box.top;
            }
            return [Math.round(x), Math.round(y), event.button, event.shiftKey ? 1 : 0];
        };
        const sendPointer = (index, fields) =>
            Module._marmelade_browser_dispatch_pointer(
                index, fields[0], fields[1], fields[2], fields[3]);

        // Moves are coalesced to one per animation frame. Any other event first
        // delivers a move still waiting, so the order the player acted in holds.
        let pendingMove = null;
        const flushMove = () => {
            if (!pendingMove) return;
            const move = pendingMove;
            pendingMove = null;
            if (move.owner.isConnected &&
                move.owner.hasAttribute("data-marmelade-pointermove")) {
                sendPointer(indexOf(move.owner, "pointermove"), move.fields);
            }
        };

        mount.addEventListener("click", event => {
            flushMove();
            const owner = ownerFrom("click", event.target);
            if (owner) sendText(indexOf(owner, "click"), "");
        });
        mount.addEventListener("input", event => {
            flushMove();
            const owner = ownerFrom("input", event.target);
            if (owner) sendText(indexOf(owner, "input"), event.target.value);
        });
        for (const kind of ["pointerdown", "pointerup"]) {
            mount.addEventListener(kind, event => {
                flushMove();
                const owner = ownerFrom(kind, event.target);
                if (owner) sendPointer(indexOf(owner, kind), pointerFields(owner, event));
            });
        }
        mount.addEventListener("pointermove", event => {
            const owner = ownerFrom("pointermove", event.target);
            if (!owner) return;
            const scheduled = pendingMove !== null;
            pendingMove = { owner, fields: pointerFields(owner, event) };
            if (!scheduled) requestAnimationFrame(flushMove);
        });
        // pointerleave does not bubble, so it is derived from pointerout: every
        // owner the pointer was inside and is now outside of has been left.
        mount.addEventListener("pointerout", event => {
            const into = event.relatedTarget;
            for (let owner = ownerFrom("pointerleave", event.target);
                 owner;
                 owner = ownerFrom("pointerleave", owner.parentElement)) {
                if (into instanceof Node && owner.contains(into)) break;
                flushMove();
                sendText(indexOf(owner, "pointerleave"), "");
            }
        });
        mount.addEventListener("contextmenu", event => {
            const owner = ownerFrom("contextmenu", event.target);
            if (!owner) return;
            event.preventDefault();
            flushMove();
            sendText(indexOf(owner, "contextmenu"), "");
        });
        mount.marmeladeListeners = true;
    }
},

    browser_subscribe__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_subscribe: function(frame, key_down, key_up) {
    let subscribed = Module.marmeladeSubscriptions;
    if (!subscribed) {
        subscribed = Module.marmeladeSubscriptions =
            { frame: false, keyDown: false, keyUp: false, ticking: false };
        const scrolls = new Set([" ", "ArrowUp", "ArrowDown", "ArrowLeft", "ArrowRight",
                                 "PageUp", "PageDown"]);
        const editable = target => target instanceof Element &&
            (target.isContentEditable ||
             ["input", "textarea", "select"].includes(target.localName));
        const sendKey = (kind, event) => {
            const text = value => {
                const bytes = lengthBytesUTF8(value) + 1;
                const pointer = _malloc(bytes);
                stringToUTF8(value, pointer, bytes);
                return pointer;
            };
            const code = text(event.code);
            const key = text(event.key);
            const flags = (event.repeat ? 1 : 0) | (event.shiftKey ? 2 : 0) |
                          (event.ctrlKey ? 4 : 0);
            Module._marmelade_browser_dispatch_key(kind, code, key, flags);
            _free(code);
            _free(key);
        };
        document.addEventListener("keydown", event => {
            if (!subscribed.keyDown) return;
            // Space and the arrows would scroll the page under a game.
            if (scrolls.has(event.key) && !editable(event.target)) event.preventDefault();
            sendKey(0, event);
        });
        document.addEventListener("keyup", event => {
            if (subscribed.keyUp) sendKey(1, event);
        });
    }
    subscribed.frame = frame !== 0;
    subscribed.keyDown = key_down !== 0;
    subscribed.keyUp = key_up !== 0;
    if (subscribed.frame && !subscribed.ticking) {
        subscribed.ticking = true;
        const tick = time => {
            if (!subscribed.frame) {
                subscribed.ticking = false;
                return;
            }
            requestAnimationFrame(tick);
            Module._marmelade_browser_dispatch_frame(Math.round(time));
        };
        requestAnimationFrame(tick);
    }
},

    browser_time_now__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_time_now: function() { return performance.now(); },

    browser_local_storage_get__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_local_storage_get: function(key, key_len) {
    const value = localStorage.getItem(UTF8ToString(key, key_len));
    if (value === null) return 0;
    const bytes = lengthBytesUTF8(value) + 1;
    const pointer = _malloc(bytes);
    stringToUTF8(value, pointer, bytes);
    return pointer;
},

    browser_local_storage_set__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_local_storage_set: function(key, key_len, value, value_len) {
    localStorage.setItem(UTF8ToString(key, key_len), UTF8ToString(value, value_len));
},

    browser_local_storage_remove__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_local_storage_remove: function(key, key_len) {
    localStorage.removeItem(UTF8ToString(key, key_len));
},

    browser_local_storage_clear__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_local_storage_clear: function() { localStorage.clear(); },

    browser_yield__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_yield: function(request) {
    const resume = () => Module._marmelade_browser_yielded(request);
    if (typeof requestAnimationFrame === "function") {
        requestAnimationFrame(() => requestAnimationFrame(resume));
    } else {
        setTimeout(resume, 0);
    }
},

    browser_fetch_get__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_fetch_get: function(url, url_len, request) {
    const address = UTF8ToString(url, url_len);
    (async () => {
        let status = -1;
        let body = "";
        try {
            const response = await fetch(address);
            status = response.status;
            body = await response.text();
        } catch (error) {
            body = String(error);
        }
        const body_len = lengthBytesUTF8(body);
        const pointer = _malloc(body_len + 1);
        stringToUTF8(body, pointer, body_len + 1);
        Module._marmelade_fetch_complete(request, status, pointer, body_len);
        _free(pointer);
    })();
},

    browser_web_socket_connect__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_web_socket_connect: function(url, url_len, request) {
    if (!Module.marmeladeSockets) {
        Module.marmeladeSockets = { next: 1, open: new Map() };
    }
    const socket = new WebSocket(UTF8ToString(url, url_len));
    socket.addEventListener("open", () => {
        const handle = Module.marmeladeSockets.next++;
        Module.marmeladeSockets.open.set(handle, socket);
        Module._marmelade_web_socket_connected(request, handle);
    }, { once: true });
    socket.addEventListener("error", () => {
        Module._marmelade_web_socket_connected(request, -1);
    }, { once: true });
},

    browser_web_socket_send__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_web_socket_send: function(handle, body, body_len) {
    const socket = Module.marmeladeSockets?.open.get(handle);
    if (!socket || socket.readyState !== WebSocket.OPEN) return 0;
    socket.send(UTF8ToString(body, body_len));
    return 1;
},

    browser_web_socket_receive__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_web_socket_receive: function(handle, request) {
    const socket = Module.marmeladeSockets?.open.get(handle);
    if (!socket) {
        Module._marmelade_web_socket_received(request, 0, 0, 0);
        return;
    }
    let settled = false;
    const failed = () => {
        if (settled) return;
        settled = true;
        Module._marmelade_web_socket_received(request, 0, 0, 0);
    };
    socket.addEventListener("message", event => {
        if (settled) return;
        settled = true;
        const value = String(event.data);
        const length = lengthBytesUTF8(value);
        const pointer = _malloc(length + 1);
        stringToUTF8(value, pointer, length + 1);
        Module._marmelade_web_socket_received(request, 1, pointer, length);
        _free(pointer);
    }, { once: true });
    socket.addEventListener("error", failed, { once: true });
    socket.addEventListener("close", failed, { once: true });
},

    browser_web_socket_close__deps: ['$UTF8ToString', '$stringToUTF8', '$lengthBytesUTF8'],
    browser_web_socket_close: function(handle) {
    const socket = Module.marmeladeSockets?.open.get(handle);
    if (socket) socket.close();
    Module.marmeladeSockets?.open.delete(handle);
},

});
