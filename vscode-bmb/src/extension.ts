import * as path from 'path';
import * as vscode from 'vscode';
import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    TransportKind,
} from 'vscode-languageclient/node';

let client: LanguageClient | undefined;

export async function activate(context: vscode.ExtensionContext) {
    // Get the server path from configuration or use default
    const config = vscode.workspace.getConfiguration('bmb');
    let serverPath = config.get<string>('server.path');

    if (!serverPath) {
        // Use 'bmb-lsp' from PATH
        serverPath = 'bmb-lsp';
    }

    // Server options
    const serverOptions: ServerOptions = {
        run: {
            command: serverPath,
            transport: TransportKind.stdio,
        },
        debug: {
            command: serverPath,
            transport: TransportKind.stdio,
        },
    };

    // Client options
    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'bmb' }],
        synchronize: {
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.bmb'),
        },
        outputChannelName: 'BMB Language Server',
    };

    // Create and start the language client
    client = new LanguageClient(
        'bmb-lsp',
        'BMB Language Server',
        serverOptions,
        clientOptions
    );

    // Register commands
    context.subscriptions.push(
        vscode.commands.registerCommand('bmb.restartServer', async () => {
            if (client) {
                await client.stop();
                await client.start();
                vscode.window.showInformationMessage('BMB Language Server restarted');
            }
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('bmb.formatDocument', async () => {
            const editor = vscode.window.activeTextEditor;
            if (editor && editor.document.languageId === 'bmb') {
                await vscode.commands.executeCommand('editor.action.formatDocument');
            }
        })
    );

    // Start the client
    try {
        await client.start();
        console.log('BMB Language Server started');
    } catch (error) {
        console.error('Failed to start BMB Language Server:', error);
        vscode.window.showWarningMessage(
            'BMB Language Server could not start. Make sure bmb-lsp is installed and in your PATH. ' +
            'Syntax highlighting will still work.'
        );
    }
}

export async function deactivate(): Promise<void> {
    if (client) {
        await client.stop();
    }
}
