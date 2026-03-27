import "@radix-ui/themes/styles.css";
import './App.css';
import { Theme } from "@radix-ui/themes";
import { MainPage } from "./ChecklistPage";


function App() {
  return (
    <Theme>
      <MainPage />
    </Theme>
  );
}

export default App;
